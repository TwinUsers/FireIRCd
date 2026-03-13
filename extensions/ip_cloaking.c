/*
 * Charybdis: an advanced ircd
 * m_cloaking.c: provide user hostname cloaking
 *
 * Written originally by nenolod, altered to use FNV by Elizabeth in 2008,
 * updated to use HMAC-SHA256 for cryptographic cloaking.
 *
 * The cloaking secret is now auto-generated at module load time using
 * OpenSSL's RAND_bytes(). This produces a cryptographically random 256-bit
 * key encoded as hex and stored in cloaking_secret_hex.
 *
 * NOTE: Because the key is ephemeral, cloaks will differ across server
 * restarts and between servers in the same network. For a production
 * network, replace the generate_cloaking_secret() call in _modinit() with
 * code that reads a shared static secret from your ircd configuration and
 * writes it into cloaking_secret_hex.
 */

#include "stdinc.h"
#include "modules.h"
#include "hook.h"
#include "client.h"
#include "ircd.h"
#include "send.h"
#include "hash.h"
#include "s_conf.h"
#include "s_user.h"
#include "s_serv.h"
#include "numeric.h"

#include <openssl/hmac.h>
#include <openssl/sha.h>
#include <openssl/rand.h>

/* 256-bit key stored as lowercase hex + NUL */
#define CLOAKING_SECRET_LEN      32
#define CLOAKING_SECRET_HEX_LEN  (CLOAKING_SECRET_LEN * 2 + 1)

static char cloaking_secret_hex[CLOAKING_SECRET_HEX_LEN];

/*
 * generate_cloaking_secret
 *
 * Generates CLOAKING_SECRET_LEN random bytes via RAND_bytes() and
 * encodes them as a lowercase hex string into cloaking_secret_hex.
 *
 * Returns 1 on success, 0 if RAND_bytes() fails (e.g. entropy source
 * unavailable).
 */
static int
generate_cloaking_secret(void)
{
    unsigned char raw[CLOAKING_SECRET_LEN];
    int i;

    if (RAND_bytes(raw, sizeof(raw)) != 1)
        return 0;

    for (i = 0; i < CLOAKING_SECRET_LEN; i++)
        snprintf(cloaking_secret_hex + i * 2, 3, "%02x", (unsigned int)raw[i]);

    cloaking_secret_hex[CLOAKING_SECRET_HEX_LEN - 1] = '\0';

    /* Zero raw key material from the stack immediately after encoding. */
    memset(raw, 0, sizeof(raw));
    return 1;
}

static int
_modinit(void)
{
    if (!generate_cloaking_secret()) {
        ilog(L_MAIN, "m_cloaking: RAND_bytes() failed — cannot generate cloaking secret");
        return -1;
    }

    ilog(L_MAIN, "m_cloaking: generated ephemeral cloaking secret (first 8 chars: %.8s...)",
         cloaking_secret_hex);

    user_modes['x'] = find_umode_slot();
    construct_umodebuf();
    return 0;
}

static void
_moddeinit(void)
{
    /* Zero key material before unloading to avoid it lingering in memory. */
    memset(cloaking_secret_hex, 0, sizeof(cloaking_secret_hex));

    user_modes['x'] = 0;
    construct_umodebuf();
}

static void check_umode_change(void *data);
static void check_new_user(void *data);

mapi_hfn_list_av1 ip_cloaking_hfnlist[] = {
    { "umode_changed", (hookfn) check_umode_change },
    { "new_local_user", (hookfn) check_new_user },
    { NULL, NULL }
};

DECLARE_MODULE_AV1(ip_cloaking, _modinit, _moddeinit, NULL, NULL,
                   ip_cloaking_hfnlist, "$Revision$");

/*
 * hmac_hash_host
 *
 * Computes HMAC-SHA256 of `inbuf` keyed with `cloaking_secret_hex`, then
 * XOR-folds the 32-byte digest down to a uint32_t by processing it as
 * eight big-endian 32-bit words and XORing them together.
 *
 * This gives a stable, keyed 32-bit accumulator used by both
 * do_host_cloak_ip() and do_host_cloak_host().
 */
static uint32_t
hmac_hash_host(const char *inbuf)
{
    unsigned char digest[SHA256_DIGEST_LENGTH]; /* 32 bytes */
    unsigned int digest_len = sizeof(digest);
    uint32_t accum = 0;
    int i;

    HMAC(EVP_sha256(),
         cloaking_secret_hex, (int)strlen(cloaking_secret_hex),
         (const unsigned char *)inbuf, strlen(inbuf),
         digest, &digest_len);

    /*
     * XOR-fold the 32-byte digest into 4 bytes.
     * Each group of 4 bytes is interpreted big-endian and XORed together.
     * This preserves good diffusion while fitting the existing uint32_t API.
     */
    for (i = 0; i < SHA256_DIGEST_LENGTH; i += 4) {
        uint32_t word = ((uint32_t)digest[i]     << 24) |
                        ((uint32_t)digest[i + 1] << 16) |
                        ((uint32_t)digest[i + 2] <<  8) |
                        ((uint32_t)digest[i + 3]);
        accum ^= word;
    }

    return accum;
}

static void
distribute_hostchange(struct Client *client_p, char *newhost)
{
    if (newhost != client_p->orighost)
        sendto_one_numeric(client_p, RPL_HOSTHIDDEN, "%s :is now your hidden host",
                           newhost);
    else
        sendto_one_numeric(client_p, RPL_HOSTHIDDEN, "%s :hostname reset",
                           newhost);

    sendto_server(NULL, NULL,
                  CAP_EUID | CAP_TS6, NOCAPS, ":%s CHGHOST %s :%s",
                  use_id(&me), use_id(client_p), newhost);
    sendto_server(NULL, NULL,
                  CAP_TS6, CAP_EUID, ":%s ENCAP * CHGHOST %s :%s",
                  use_id(&me), use_id(client_p), newhost);

    change_nick_user_host(client_p, client_p->name, client_p->username, newhost, 0, "Changing host");

    if (newhost != client_p->orighost)
        SetDynSpoof(client_p);
    else
        ClearDynSpoof(client_p);
}

/*
 * do_host_cloak_ip
 *
 * For IPv4 (a.b.c.d): replaces the last octet with an 8-char hex digest,
 * producing e.g. "192.168.1.a3f9c21b".
 *
 * For IPv6: replaces the second half of the address (after the midpoint
 * colon group) with a single 8-char hex token, e.g.
 * "2001:db8::a3f9c21b".
 *
 * The prefix is kept so users can still see their general network location,
 * while the host-identifying suffix is replaced by a short keyed digest.
 */
static void
do_host_cloak_ip(const char *inbuf, char *outbuf)
{
    char hash_str[9]; /* 8 hex chars + NUL */
    uint32_t accum = hmac_hash_host(inbuf);
    const char *last_sep;

    snprintf(hash_str, sizeof(hash_str), "%08x", accum);

    if (strchr(inbuf, ':')) {
        /* IPv6: keep first half up to the midpoint colon, append digest */
        int colons = 0, total = 0;
        const char *p;
        const char *mid = NULL;

        for (p = inbuf; *p; p++)
            if (*p == ':')
                total++;

        for (p = inbuf; *p; p++) {
            if (*p == ':') {
                colons++;
                if (colons == total / 2) {
                    mid = p;
                    break;
                }
            }
        }

        if (mid == NULL || !strchr(inbuf, ':')) {
            rb_strlcpy(outbuf, inbuf, HOSTLEN + 1);
            return;
        }

        snprintf(outbuf, HOSTLEN + 1, "%.*s:%s",
                 (int)(mid - inbuf), inbuf, hash_str);
    } else if ((last_sep = strrchr(inbuf, '.')) != NULL) {
        /* IPv4: replace last octet */
        snprintf(outbuf, HOSTLEN + 1, "%.*s.%s",
                 (int)(last_sep - inbuf), inbuf, hash_str);
    } else {
        rb_strlcpy(outbuf, inbuf, HOSTLEN + 1);
    }
}

/*
 * do_host_cloak_host
 *
 * Replaces the first label of a hostname with an 8-char hex digest,
 * keeping the rest of the domain intact.
 * e.g. "host123.isp.example.com" -> "a3f9c21b.isp.example.com"
 */
static void
do_host_cloak_host(const char *inbuf, char *outbuf)
{
    char hash_str[9]; /* 8 hex chars + NUL */
    uint32_t accum = hmac_hash_host(inbuf);
    const char *dot;

    snprintf(hash_str, sizeof(hash_str), "%08x", accum);

    dot = strchr(inbuf, '.');
    if (dot != NULL)
        snprintf(outbuf, HOSTLEN + 1, "%s%s", hash_str, dot);
    else
        rb_strlcpy(outbuf, hash_str, HOSTLEN + 1);
}

static void
check_umode_change(void *vdata)
{
    hook_data_umode_changed *data = (hook_data_umode_changed *)vdata;
    struct Client *source_p = data->client;

    if (!MyClient(source_p))
        return;

    if (!((data->oldumodes ^ source_p->umodes) & user_modes['x']))
        return;

    if (source_p->umodes & user_modes['x']) {
        if (IsIPSpoof(source_p) || source_p->localClient->mangledhost == NULL ||
            (IsDynSpoof(source_p) && strcmp(source_p->host, source_p->localClient->mangledhost))) {
            source_p->umodes &= ~user_modes['x'];
            return;
        }
        if (strcmp(source_p->host, source_p->localClient->mangledhost)) {
            distribute_hostchange(source_p, source_p->localClient->mangledhost);
        } else
            sendto_one_numeric(source_p, RPL_HOSTHIDDEN, "%s :is now your hidden host",
                               source_p->host);
    } else if (!(source_p->umodes & user_modes['x'])) {
        if (source_p->localClient->mangledhost != NULL &&
            !strcmp(source_p->host, source_p->localClient->mangledhost)) {
            distribute_hostchange(source_p, source_p->orighost);
        }
    }
}

static void
check_new_user(void *vdata)
{
    struct Client *source_p = (void *)vdata;

    if (IsIPSpoof(source_p)) {
        source_p->umodes &= ~user_modes['x'];
        return;
    }
    source_p->localClient->mangledhost = rb_malloc(HOSTLEN + 1);
    if (!irccmp(source_p->orighost, source_p->sockhost))
        do_host_cloak_ip(source_p->orighost, source_p->localClient->mangledhost);
    else
        do_host_cloak_host(source_p->orighost, source_p->localClient->mangledhost);
    if (IsDynSpoof(source_p))
        source_p->umodes &= ~user_modes['x'];
    if (source_p->umodes & user_modes['x']) {
        rb_strlcpy(source_p->host, source_p->localClient->mangledhost, sizeof(source_p->host));
        if (irccmp(source_p->host, source_p->orighost))
            SetDynSpoof(source_p);
    }
}
