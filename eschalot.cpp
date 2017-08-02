/* eschalot - generates vanity .onion names using brute-force hashing.
 * A fork of shallot, which was a fork of onionhash. */

/*
 * Copyright (c) 2013 Unperson Hiro <blacksunhq56imku.onion>
 * Copyright (c) 2007 Orum          <hangman5naigg7rr.onion>
 * Copyright (c) 2006 Cowboy Bebop  <torlandypjxiligx.onion>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

/* Lets agree on 100 characters line limit, tab is 8 spaces long, second level ident is 4 spaces. */
/* ---------- This wide ------------------------------------------------------------------------- */

#ifdef __APPLE__
#include <libkern/OSByteOrder.h>

#define htobe16(x) OSSwapHostToBigInt16(x)
#define htole16(x) OSSwapHostToLittleInt16(x)
#define be16toh(x) OSSwapBigToHostInt16(x)
#define le16toh(x) OSSwapLittleToHostInt16(x)

#define htobe32(x) OSSwapHostToBigInt32(x)
#define htole32(x) OSSwapHostToLittleInt32(x)
#define be32toh(x) OSSwapBigToHostInt32(x)
#define le32toh(x) OSSwapLittleToHostInt32(x)

#define htobe64(x) OSSwapHostToBigInt64(x)
#define htole64(x) OSSwapHostToLittleInt64(x)
#define be64toh(x) OSSwapBigToHostInt64(x)
#define le64toh(x) OSSwapLittleToHostInt64(x)
#endif  /* __APPLE__ */

#if defined(__linux__) || defined(__CYGWIN__)
# define _GNU_SOURCE

#include <endian.h>

#endif

#ifdef __FreeBSD__
# include <sys/endian.h>
#endif

#include <sys/types.h>

#include <cctype>
#include <getopt.h>
#include <cinttypes>
#include <pthread.h>
#include <regex.h>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include <iostream>

#include <openssl/bn.h>
#include <openssl/pem.h>

#include "debug.h"

#define OPENSSL_VERSION_1_1 0x10100000L

/* Define NEED_HTOBE32 if htobe32() is not available on your platform. */
/* #define NEED_HTOBE32 */
#if BYTE_ORDER == LITTLE_ENDIAN
# ifdef NEED_HTOBE32
#  define HTOBE32(x)	(((uint32_t)(x) & 0xffu)	<< 24 |	\
             ((uint32_t)(x) & 0xff00u)	<<  8 |	\
             ((uint32_t)(x) & 0xff0000u)	>>  8 |	\
             ((uint32_t)(x) & 0xff000000u)	>> 24)
# else
#  define HTOBE32(x)    htobe32(x)
# endif
#else
# define HTOBE32(x)	(x)
#endif

/* Define NEED_STRNLEN if strnlen() is not available on your platform. */
/* #define NEED_STRNLEN */
#ifdef NEED_STRNLEN
static size_t		strnlen(const char *, size_t);
size_t
strnlen(const char *s, size_t ml)
{
    unsigned int i;
    for (i = 0; *(s + i) != '\0' && i < ml; i++)
        ;
    return i;
}
#endif


#define VERSION        "1.2.0"
#define SHA_REL_CTX_LEN    (10 * sizeof(SHA_LONG))    /* 40 bytes */
#define RSA_KEYS_BITLEN    1024            /* RSA key length to use */
#define SIZE_OF_E    4            /* Limit public exponent to 4 bytes */
#define RSA_E_START    (0xFFFFFFu + 2)        /* Min e */
#define RSA_E_LIMIT    0xFFFFFFFFu        /* Max e */
#define ONION_LENP1    17            /* Onion name length plus 1 */
#define MAX_THREADS    100            /* Maximum number of threads */
#define MAX_WORDS    0xFFFFFFFFu        /* Maximum words to read from file */
#define BASE32_ALPHABET    "abcdefghijklmnopqrstuvwxyz234567"

extern char *__progname;

/* Error and debug functions */
static void usage();

static void (*msg)(char *, ...);

/* User IO functions */
static void setoptions(int argc, char *argv[]);

static void readfile();

static void printresult(RSA *rsa, uint8_t *target, uint8_t *actual);

/* Math and search functions */
static bool fsearch(uint8_t *buf, uint8_t *onion);

static bool psearch(uint8_t *buf, uint8_t *onion);

static bool rsearch(uint8_t *buf, uint8_t *onion);

static bool (*search)(uint8_t *, uint8_t *);

static bool validkey(RSA *rsa);

static signed int compare(const void *a, const void *b);

static void base32_enc(uint8_t *dst, const uint8_t *src);

static void base32_dec(uint8_t *dst, const uint8_t *src);

static void onion_enc(uint8_t *onion, RSA *rsa);

static void zerobits(uint16_t *ind, uint64_t *word,
                     uint8_t *buffer, unsigned int length);

/* Main thread routine */
static void *worker(void *arg);

/* Global variables */
/* TODO: perhaps getting rid of so many globals is in order... */
bool done, cflag, fflag, nflag, pflag, rflag, vflag;
unsigned int minlen, maxlen, threads, prefixlen, wordcount;
char fn[FILENAME_MAX + 1], prefix[ONION_LENP1];
regex_t *regex;

pthread_mutex_t printresult_lock;

struct {
    unsigned int count;
    uint64_t *branch;
} tree[65536] = {{0, nullptr}};

int
main(int argc, char *argv[]) {
    pthread_t babies[MAX_THREADS];
    uint64_t count[MAX_THREADS];
    unsigned int i, j, dupcount = 0;

    pthread_mutex_init(&printresult_lock, nullptr);

    /* Initialize global flags */
    wordcount = static_cast<unsigned int>(done = cflag = fflag = nflag = pflag = rflag = vflag = false);
    minlen = 8;
    maxlen = 16;
    threads = 1;
    msg = normal;    /* Default: non-verbose */
    search = nullptr;    /* No default search, has to be specified */

    try {
        setoptions(argc, argv);
    } catch (const char* a) {
        std::cout << "Error: " << a << std::endl;
        exit(1);
    } catch (...) {
        std::cout << "Error: Unknown exception caught." << std::endl;
        exit(1);
    }
    if (fflag) {
        readfile();
        msg(const_cast<char *>("Sorting the word hashes and removing duplicates.\n"));
        wordcount = 0;
        for (i = 0; i < 65536; i++) {
            dupcount = 0;
            qsort(tree[i].branch, tree[i].count, sizeof(tree[i].branch[0]), &compare);
            for (j = 1; j < tree[i].count; j++) {
                if (tree[i].branch[j] == tree[i].branch[j - 1]) {
                    tree[i].branch[j - 1] = 0xFFFFFFFFFFFFFFFFu;
                    dupcount++;
                }
            }

            if (dupcount > 0) {
                qsort(tree[i].branch, tree[i].count, sizeof(tree[i].branch[0]),
                      &compare);
                tree[i].count -= dupcount;
            }
            wordcount += tree[i].count;
        }
        msg(const_cast<char *>("Final word count: %d.\n"), wordcount);
    }


    try {
        /* Start our threads */
        for (i = 1; i <= threads; i++) {
            count[i] = 0;
            if (pthread_create(&babies[i], nullptr, worker, (void *) &count[i]) != 0)
                throw "Failed to start thread!";
            msg(const_cast<char *>("Thread #%d started.\n"), i);
        }
    } catch (const char* a) {
        std::cout << "Error: " << a << std::endl;
        exit(1);
    } catch (...) {
        std::cout << "Error: Caught unknown exception." << std::endl;
        exit(1);
    }

    /* Monitor performance
     * TODO: redo this whole thing, add estimate time for keys */
    if (vflag) {
        uint64_t loops;
        time_t elapsed, start = time(nullptr);
        unsigned int delay = 5;

        msg(const_cast<char *>("Running, collecting performance data...\n"));
        for (;;) {
            sleep(delay *= 2);
            if (done)
                return 0;

            /* Collect our thread's counters */
            loops = 0;
            i = threads;
            do {
                loops += count[i];
            } while (--i != 0u);

            /* On a really slow machine the initial delay might not be
             * enough to generate the first RSA key, so give it more time. */
            if (loops == 0)
                continue;

            elapsed = time(nullptr) - start;

            /* Bug here somewhere - with pcc compiler only. */
            /* TODO: Fix. */
            msg(const_cast<char *>("Total hashes: %" PRIu64
                        ", running time: %d seconds, hashes per second: % estamated time: %" PRIu64 "\n"),
                loops, elapsed, (uint64_t) (loops / elapsed),
                (uint64_t) (loops / elapsed) / strlen((const char *) msg));
        }
    }
    /* Wait for all the threads to exit */
    for (i = 1; i <= threads; i++)
        pthread_join(babies[i], nullptr);
    exit(0);
}

/* Main hashing thread */
void *
worker(void *arg) {
    SHA_CTX hash = {}, copy = {};
    RSA *rsa = nullptr;
    uint8_t *tmp, *der,
            buf[SHA_DIGEST_LENGTH],
            onion[ONION_LENP1],
            onionfinal[ONION_LENP1];
    signed int derlen;
    uint64_t *counter;
    /* Public exponent and the "big-endian" version of it */
    unsigned int e, e_be;
    BIGNUM *big_e = BN_new();
    BN_set_word(big_e, (unsigned long) RSA_E_START);

    counter = (uint64_t *) arg;

    while (!done) {
        /* Generate a new RSA key every time e reaches RSA_E_LIMIT */
#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
        rsa = RSA_new();
        if (!RSA_generate_key_ex(rsa, RSA_KEYS_BITLEN, big_e, NULL))
            throw "RSA Key Generation failed!";
#else
        rsa = RSA_generate_key(RSA_KEYS_BITLEN, RSA_E_START,
                               nullptr, nullptr);
        if (rsa == nullptr)
            throw "RSA Key Generation failed!";
#endif

        /* Too chatty - disable. */
        /* msg("Generated a new RSA key pair.\n"); */

        /* Encode RSA key in X.690 DER format */
        if ((derlen = i2d_RSAPublicKey(rsa, nullptr)) < 0)
            throw "DER encoding failed!";
        if ((der = tmp = (uint8_t *) malloc((size_t) derlen)) == nullptr)
            throw "malloc(derlen) failed!";
        if (i2d_RSAPublicKey(rsa, &tmp) != derlen)
            throw "DER encoding failed!";

        /* Prepare the hash context */
        SHA1_Init(&hash);
        SHA1_Update(&hash, der, (size_t) (derlen - SIZE_OF_E));
        free(der);
        e = RSA_E_START - 2; /* public exponent */
        BN_set_word(big_e, (unsigned long) e);

        /* Main loop */
        while ((e < RSA_E_LIMIT) && !done) {
            e += 2;
            /* Convert e to big-endian format. */
            e_be = HTOBE32(e);
            /* Copy the relevant parts of already set up context. */
            memcpy(&copy, &hash, SHA_REL_CTX_LEN); /* 40 bytes */
            copy.num = hash.num;
            /* Compute SHA1 digest (the real bottleneck) */
            SHA1_Update(&copy, &e_be, SIZE_OF_E);
            SHA1_Final(buf, &copy);
            (*counter)++;
            /* This is fairly fast, but can be faster if inlined. */
            base32_enc(onion, buf);

            /* The search speed varies based on the mode we are in.
             * Regex's performance depends on the expression used.
             * Fixed prefix is as fast as memcmp(3).
             * Wordlist performance depends on (mostly):
             *   number of "lengths" to search for (-l from-to);
             *   number of unique words loaded from file.
             *
             * Inlining everything and optimizing for one mode and
             * fixed word length improved the performance somewhat
             * when I tried it, but it's not worth it. */
            if (search(buf, onion)) {
                /* Found a possible key,
                 * from here on down performance is not critical. */
#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
                BIGNUM *new_e;
                new_e = BN_bin2bn((uint8_t *)&e_be, SIZE_OF_E, NULL);
                if (new_e == NULL)
                    throw "Failed to convert e to BIGNUM!";
                if(!RSA_set0_key(rsa, NULL, new_e, NULL))
                    throw "Failed to set e in RSA key!";
#else
                if (BN_bin2bn((uint8_t *) &e_be, SIZE_OF_E, rsa->e) == nullptr)
                    throw "Failed to set e in RSA key!";
#endif
                if (!validkey(rsa))
                    throw "A bad key was found!";
                if (pflag)
                    onion[prefixlen] = '\0';

                onion_enc(onionfinal, rsa);

                /* Every so often the onion found matches
                 * whatever we were looking for, but the final
                 * generated onion is garbage. I suspect a CPU
                 * or RAM overheating, but it could be a subtle
                 * bug somewhere. Hard to pin-point. According
                 * to the reports I've seen, shallot has had a
                 * similar problem.
                 *
                 * Happens most often in a wordlist search mode,
                 * but I think I have seen it in a regex mode
                 * as well. Does not seem to happen in a fixed
                 * prefix mode.
                 *
                 * Adding this check to avoid producing garbage
                 * results and to alleviate the problem a bit. */
                if (strncmp((char *) onion, (char *) onionfinal,
                            (!rflag ? strnlen((char *) onion, ONION_LENP1) : 16)) != 0) {
                    msg(const_cast<char *>("\nWARNING! Error detected! CPU/RAM overheating?\n"));
                    msg(const_cast<char *>("Found %s, but finalized to %s.\n"),
                        (char *) onion, (char *) onionfinal);
                    msg(const_cast<char *>("Suspending this thread for 30 seconds.\n"));
                    sleep(30);
                    msg(const_cast<char *>("Generating new RSA key.\n\n"));
                    break;
                }

                pthread_mutex_lock(&printresult_lock);
                try {
                    printresult(rsa, onion, onionfinal);
                } catch (const char* a) {
                    std::cout << "Error: " << a << std::endl;
                }
                pthread_mutex_unlock(&printresult_lock);


                if (!cflag)
                    done = true; /* Notify other threads. */
                break;
            }
        }
        RSA_free(rsa);
    }
    return nullptr;
}

/* Read words from file */
void readfile() {
    FILE *file;
    uint8_t w[ONION_LENP1] = {0}, buf[10];
    uint8_t len, j;
    uint16_t ind;
    signed int c;
    uint64_t wrd;
    bool inword;

    if ((file = fopen(fn, "r")) == nullptr)
        std::cout << (const_cast<char *>("Failed to open %s!\n"), fn);
    msg(const_cast<char *>("Reading words from %s, please wait...\n"), fn);

    /* We have to inspect each character individually anyway,
     * so lets just use fgetc here and let the OS buffer stuff. */
    j = 0;
    while ((c = fgetc(file)) != EOF) {
        c = tolower(c);
        inword = false;
        /* Only load words with digits if the -n option was used. */
        if ((c >= 'a' && c <= 'z') || (nflag && c >= '2' && c <= '7')) {
            w[j++] = (uint8_t) c;
            inword = true;
        }

        if ((!inword && j > 0) || j > 16) {
            /* We clip the words longer than 16 characters here. */
            w[j] = '\0';
            j = 0;
            /* Only pick the words of the length we need. */
            len = (uint8_t) strnlen((char *) w, ONION_LENP1);
            if (len >= minlen && len <= maxlen && wordcount < MAX_WORDS) {
                base32_dec(buf, w);
                memset(w, 0, sizeof(w));
                zerobits(&ind, &wrd, buf, len);

                if ((tree[ind].branch = (uint64_t *) realloc(tree[ind].branch,
                                                             sizeof(uint64_t) * (tree[ind].count + 1))) == nullptr)
                    std::cout << const_cast<char *>("realloc() failed!\n");

                tree[ind].branch[tree[ind].count] = wrd;
                tree[ind].count++;
                wordcount++;
            }
        }
    }
    fclose(file);

    if (wordcount == 0)
        std::cout << (const_cast<char *>("Could not find any valid words in %s!\n"), fn);
    else
        msg(const_cast<char *>("Loaded %d words.\n"), wordcount);
}

/* Check if the RSA key is ok (PKCS#1 v2.1). */
bool validkey(RSA *rsa) {
    BN_CTX *ctx = BN_CTX_new();
    BN_CTX_start(ctx);
    BIGNUM *p1 = BN_CTX_get(ctx),        /* p - 1 */
            *q1 = BN_CTX_get(ctx),        /* q - 1 */
            *gcd = BN_CTX_get(ctx),        /* GCD(p - 1, q - 1) */
            *lambda = BN_CTX_get(ctx),    /* LCM(p - 1, q - 1) */
            *tmp = BN_CTX_get(ctx);        /* temporary storage */
#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
    BIGNUM const *n = BN_CTX_get(ctx),
                 *e = BN_CTX_get(ctx),
                 *d = BN_CTX_get(ctx);
    BIGNUM const *p = BN_CTX_get(ctx),
                 *q = BN_CTX_get(ctx);
    BIGNUM const *dmp1 = BN_CTX_get(ctx),
                 *dmq1 = BN_CTX_get(ctx),
                 *iqmp = BN_CTX_get(ctx);

    RSA_get0_key(rsa, &n, &e, &d);
    if (n == NULL || e == NULL || d == NULL)
        throw "RSA_get0_key() failed!";

    RSA_get0_factors(rsa, &p, &q);
    if (p == NULL || q == NULL)
        throw "RSA_get0_factors() failed!";

    RSA_get0_crt_params(rsa, &dmp1, &dmq1, &iqmp);
    if (dmp1 == NULL || dmq1 == NULL || iqmp == NULL)
        throw "RSA_get0_crt_params() failed!";

    BN_sub(p1, p, BN_value_one());	/* p - 1 */
    BN_sub(q1, q, BN_value_one());	/* q - 1 */
#else
    BN_sub(p1, rsa->p, BN_value_one());    /* p - 1 */
    BN_sub(q1, rsa->q, BN_value_one());    /* q - 1 */
#endif
    BN_gcd(gcd, p1, q1, ctx);        /* gcd(p - 1, q - 1) */

    BN_div(tmp, nullptr, p1, gcd, ctx);
    BN_mul(lambda, q1, tmp, ctx);        /* lambda(n) */

    /* Check if e is coprime to lambda(n). */
#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
    BN_gcd(tmp, lambda, e, ctx);
#else
    BN_gcd(tmp, lambda, rsa->e, ctx);
#endif
    if (!BN_is_one(tmp)) {
        verbose(const_cast<char *>("WARNING: Key check failed - e is coprime to lambda!\n"));
        return false;
    }

    /* Check if public exponent e is less than n - 1. */
    /* Subtract n from e to avoid checking BN_is_zero. */
#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
    BN_sub(tmp, n, BN_value_one());
    if (BN_cmp(e, tmp) >= 0) {
        verbose("WARNING: Key check failed - e is less than (n - 1)!\n");
        return 0;
    }
#else
    BN_sub(tmp, rsa->n, BN_value_one());
    if (BN_cmp(rsa->e, tmp) >= 0) {
        verbose(const_cast<char *>("WARNING: Key check failed - e is less than (n - 1)!\n"));
        return false;
    }
#endif

#if OPENSSL_VERSION_NUMBER >= OPENSSL_VERSION_1_1
    BIGNUM *new_d = BN_new(),
           *new_dmp1 = BN_new(),
           *new_dmq1 = BN_new(),
           *new_iqmp = BN_new();

    BN_mod_inverse(new_d, e, lambda, ctx);	/* d */
    BN_mod(new_dmp1, new_d, p1, ctx);		/* d mod(p - 1) */
    BN_mod(new_dmq1, new_d, q1, ctx);		/* d mod(q - 1) */
    BN_mod_inverse(new_iqmp, q, p, ctx);	/* q ^ -1 mod p */

    if (!RSA_set0_key(rsa, NULL, NULL, new_d))
        throw "RSA_set0_key() failed!";

    if (!RSA_set0_crt_params(rsa, new_dmp1, new_dmq1, new_iqmp))
        throw "RSA_set0_crt_params() failed!";
#else
    BN_mod_inverse(rsa->d, rsa->e, lambda, ctx);    /* d */
    BN_mod(rsa->dmp1, rsa->d, p1, ctx);        /* d mod(p - 1) */
    BN_mod(rsa->dmq1, rsa->d, q1, ctx);        /* d mod(q - 1) */
    BN_mod_inverse(rsa->iqmp, rsa->q, rsa->p, ctx);    /* q ^ -1 mod p */
#endif
    BN_CTX_end(ctx);
    BN_CTX_free(ctx);

    /* In theory this should never be true,
     * unless the guy before me made a mistake ;). */
    if (RSA_check_key(rsa) != 1) {
        verbose(const_cast<char *>("WARNING: OpenSSL's RSA_check_key(rsa) failed!\n"));
        return false;
    }
    return true;
}

/* Base32 encode 10 byte long 'src' into 16 character long 'dst'
 * Experimental, unroll everything. So far, it seems to be the fastest of the
 * algorithms that I've tried.
 * TODO: review and decide if it's final.
 */
void
base32_enc(uint8_t *dst, const uint8_t *src) {
    dst[0] = (uint8_t) BASE32_ALPHABET[(src[0] >> 3)];
    dst[1] = (uint8_t) BASE32_ALPHABET[((src[0] << 2) | (src[1] >> 6)) & 31];
    dst[2] = (uint8_t) BASE32_ALPHABET[(src[1] >> 1) & 31];
    dst[3] = (uint8_t) BASE32_ALPHABET[((src[1] << 4) | (src[2] >> 4)) & 31];
    dst[4] = (uint8_t) BASE32_ALPHABET[((src[2] << 1) | (src[3] >> 7)) & 31];
    dst[5] = (uint8_t) BASE32_ALPHABET[(src[3] >> 2) & 31];
    dst[6] = (uint8_t) BASE32_ALPHABET[((src[3] << 3) | (src[4] >> 5)) & 31];
    dst[7] = (uint8_t) BASE32_ALPHABET[src[4] & 31];

    dst[8] = (uint8_t) BASE32_ALPHABET[(src[5] >> 3)];
    dst[9] = (uint8_t) BASE32_ALPHABET[((src[5] << 2) | (src[6] >> 6)) & 31];
    dst[10] = (uint8_t) BASE32_ALPHABET[(src[6] >> 1) & 31];
    dst[11] = (uint8_t) BASE32_ALPHABET[((src[6] << 4) | (src[7] >> 4)) & 31];
    dst[12] = (uint8_t) BASE32_ALPHABET[((src[7] << 1) | (src[8] >> 7)) & 31];
    dst[13] = (uint8_t) BASE32_ALPHABET[(src[8] >> 2) & 31];
    dst[14] = (uint8_t) BASE32_ALPHABET[((src[8] << 3) | (src[9] >> 5)) & 31];
    dst[15] = (uint8_t) BASE32_ALPHABET[src[9] & 31];

    dst[16] = '\0';
}

/* Decode base32 16 character long 'src' into 10 byte long 'dst'. */
/* TODO: Revisit and review, would like to shrink it down a bit.
 * However, it has to stay endian-safe and be fast. */
void
base32_dec(uint8_t *dst, const uint8_t *src) {
    uint8_t tmp[ONION_LENP1];
    unsigned int i;

    for (i = 0; i < 16; i++) {
        if (src[i] >= 'a' && src[i] <= 'z') {
            tmp[i] = (uint8_t) (src[i] - 'a');
        } else {
            if (src[i] >= '2' && src[i] <= '7')
                tmp[i] = (uint8_t) (src[i] - '1' + ('z' - 'a'));
            else {
                /* Bad character detected.
                 * This should not happen, but just in case
                 * we will replace it with 'z' character. */
                tmp[i] = 26;
            }
        }
    }
    dst[0] = (tmp[0] << 3) | (tmp[1] >> 2);
    dst[1] = (tmp[1] << 6) | (tmp[2] << 1) | (tmp[3] >> 4);
    dst[2] = (tmp[3] << 4) | (tmp[4] >> 1);
    dst[3] = (tmp[4] << 7) | (tmp[5] << 2) | (tmp[6] >> 3);
    dst[4] = (tmp[6] << 5) | tmp[7];
    dst[5] = (tmp[8] << 3) | (tmp[9] >> 2);
    dst[6] = (tmp[9] << 6) | (tmp[10] << 1) | (tmp[11] >> 4);
    dst[7] = (tmp[11] << 4) | (tmp[12] >> 1);
    dst[8] = (tmp[12] << 7) | (tmp[13] << 2) | (tmp[14] >> 3);
    dst[9] = (tmp[14] << 5) | tmp[15];
}

/* Print found .onion name and PEM formatted RSA key. */
void
printresult(RSA *rsa, uint8_t *target, uint8_t *actual) {
    uint8_t *dst;
    BUF_MEM *buf;
    BIO *b;

    b = BIO_new(BIO_s_mem());

    PEM_write_bio_RSAPrivateKey(b, rsa, nullptr, nullptr, 0, nullptr, nullptr);
    BIO_get_mem_ptr(b, &buf);
    (void) BIO_set_close(b, BIO_NOCLOSE);
    BIO_free(b);

    if ((dst = (uint8_t *) malloc(buf->length + 1)) == nullptr)
        throw "malloc(buf->length + 1) failed!\n";
    memcpy(dst, buf->data, buf->length);

    dst[buf->length] = '\0';

    msg(const_cast<char *>("Found a key for %s (%d) - %s.onion\n"),
        target, strnlen((char *) target, ONION_LENP1), actual);
    sleep(static_cast<unsigned int>(0.01)); // Somehow, without sleep(), the output is broken.
    std::cout << "-----<===###################===>-----\n";
    std::cout << actual << ".onion" << std::endl;
    std::cout << dst << std::endl;
    fflush(stdout);

    BUF_MEM_free(buf);
    free(dst);

    if (static_cast<int>(cflag) == 0) {
        exit(0);
    }
}

/* Generate .onion name from the RSA key. */
/* (using the same method as the official TOR client) */
void
onion_enc(uint8_t *onion, RSA *rsa) {
    uint8_t *bufa, *bufb, digest[SHA_DIGEST_LENGTH];
    signed int derlen;

    if ((derlen = i2d_RSAPublicKey(rsa, nullptr)) < 0)
        throw "DER encoding failed!\n";

    if ((bufa = bufb = (uint8_t *) malloc((size_t) derlen)) == nullptr)
        throw "malloc(derlen) failed!\n";

    if (i2d_RSAPublicKey(rsa, &bufb) != derlen)
        throw "DER encoding failed!\n";

    SHA1(bufa, (size_t) derlen, digest);
    free(bufa);
    base32_enc(onion, digest);
}

/* Compare function for qsort(3). */
signed int
compare(const void *a, const void *b) {
    if (*((const uint64_t *) a) > *((const uint64_t *) b))
        return 1;
    if (*((const uint64_t *) a) < *((const uint64_t *) b))
        return -1;
    return 0;
}

/* Wordlist mode search. */
bool
fsearch(uint8_t *buf, uint8_t *onion) {
    unsigned int i;
    uint16_t ind;
    uint64_t wrd;

    if (!nflag)
        for (i = 0; i < minlen; i++)
            if (onion[i] < 'a')
                return false;

    for (i = minlen; i <= maxlen; i++) {
        if (!nflag && onion[i - 1] < 'a')
            return false;

        zerobits(&ind, &wrd, buf, i);

        if (tree[ind].branch != nullptr &&
            (bsearch(&wrd, tree[ind].branch, tree[ind].count,
                     sizeof(tree[ind].branch[0]), &compare) != nullptr)) {
            onion[i] = '\0';
            return true;
        }
    }
    return false;
}

/* Regex mode search. */
bool
rsearch(__attribute__((unused)) uint8_t *buf, uint8_t *onion) {
    return regexec(regex, (char *) onion, 0, nullptr, 0) == 0;
}

/* Fixed prefix mode search. */
bool
psearch(__attribute__((unused)) uint8_t *buf, uint8_t *onion) {
    return memcmp(onion, prefix, prefixlen) == 0;
}

/* Zero unused bits, split 10 byte 'buffer' into 2 byte 'ind' and 8 byte 'word'. */
/* TODO: currently doing '1' fill instead of zeroes - decide if it's final. */
void
zerobits(uint16_t *ind, uint64_t *word, uint8_t *buffer, unsigned int length) {
    uint8_t bufcopy[10];
    unsigned int usedbytes, usedbits;

    memcpy(bufcopy, buffer, 10);
    usedbytes = length * 5 / 8;
    usedbits = length * 5 % 8;

    if (usedbits != 0u) {
        /* Lets try '1' fill instead of zeroes.. */
        /* bufcopy[usedbytes] &= (0xFFu << (8 - usedbits)); */
        bufcopy[usedbytes] |= (0xFFu >> usedbits);
        usedbytes++;
    }

    if (usedbytes < 10) {
        /* Lets try '1' fill instead of zeroes.. */
        /* memset(&bufcopy[usedbytes], 0, 10 - usedbytes); */
        memset(&bufcopy[usedbytes], 0xFFu, 10 - usedbytes);
    }

    memcpy(ind, &bufcopy[0], 2);
    memcpy(word, &bufcopy[2], 8);
}

/* Read arguments and set global variables. */
void
setoptions(int argc, char *argv[]) {
    int ch;

    while ((ch = getopt(argc, argv, "cnvt:l:f:p:r:")) != -1)
        switch (ch) {
            case 'c':
                cflag = true;
                break;
            case 'n':
                nflag = true;
                break;
            case 'v':
                vflag = true;
                msg = verbose;
                break;
            case 't':
                threads = (unsigned int) strtoul(optarg, nullptr, 0);
                if (threads < 1)
                    usage();
                if (threads > MAX_THREADS)
                    threads = MAX_THREADS;
                break;
            case 'l':
                minlen = (unsigned int) strtoul(optarg, nullptr, 0);
                if (minlen < 8 || minlen > 16 || (strchr(optarg, '-') == nullptr))
                    usage();
                maxlen = (unsigned int) strtoul(strchr(optarg, '-') + 1, nullptr, 0);
                if (maxlen < 8 || maxlen > 16 || minlen > maxlen)
                    usage();
                break;
            case 'f':
                fflag = true;
                strncpy(fn, optarg, FILENAME_MAX);
                search = fsearch;
                break;
            case 'p':
                pflag = true;
                strncpy(prefix, optarg, ONION_LENP1);
                minlen = maxlen = prefixlen = (unsigned int) strnlen(prefix, ONION_LENP1);
                if (prefixlen > 16 || prefixlen < 1)
                    usage();
                for (unsigned int i = 0; i < prefixlen; i++) {
                    prefix[i] = (char) tolower(prefix[i]);
                    if ((isalpha(prefix[i]) == 0) && (!nflag || (isdigit(prefix[i]) == 0) ||
                                                prefix[i] < '2' || prefix[i] > '7'))
                        usage();
                }
                search = psearch;
                break;
            case 'r':
                rflag = true;
                minlen = 1;
                maxlen = 16;
                if ((regex = (regex_t *) malloc(sizeof(regex_t))) == nullptr)
                    throw "malloc(sizeof(regex_t)) failed!";

                /* Do not use ICASE - too slow. */
                if (regcomp(regex, optarg, REG_EXTENDED | REG_NOSUB) != 0)
                    throw "Failed to compile regex expression!";
                search = rsearch;
                break;
            default:
                usage();
                /* NOTREACHED */
        }

    if (static_cast<int>(fflag) + static_cast<int>(rflag) + static_cast<int>(pflag) != 1)
        usage();

    std::cout << "Verbose, ";
    cflag ? std::cout << "continuous, " : std::cout << "single result, ";
    nflag ? std::cout << "digits ok, " : std::cout << "no digits, ";
    std::cout << threads << " thread(s), prefixes " << minlen << '-' << maxlen << " characters long.\n";
}

/* Print usage information and exit. */
void usage() {
    std::cout <<
              "Version: " << VERSION << '\n'
              << "\n"
              << "usage:\n"
              << __progname << " [-c] [-v] [-t count] ([-n] [-l min-max] -f filename) | (-r regex) | (-p prefix)\n"
              << "  -v         : verbose mode - print extra information to COUT\n"
              << "  -c         : continue searching after the hash is found\n"
              << "  -t count   : number of threads to spawn default is one)\n"
              << "  -l min-max : look for prefixes that are from 'min' to 'max' characters long\n"
              << "  -n         : Allow digits to be part of the prefix (affects wordlist mode only)\n"
              << "  -f filename: name of the text file with a list of prefixes\n"
              << "  -p prefix  : single prefix to look for (1-16 characters long)\n"
              << "  -r regex   : search for a POSIX-style regular expression\n"
              << "\n"
              << "Examples:\n"
              << __progname << " -cvt4 -l8-12 -f wordlist.txt >> results.txt\n"
              << "               -v -r '^test|^exam'\n"
              << "               -ct5 -p test\n\n";

    std::cout <<
              "  base32 alphabet allows letters [a-z] and digits [2-7]\nRegex pattern examples:\n"
              << "    xxx           must contain 'xxx'\n"
              << "    ^foo          must begin with 'foo'\n"
              << "    bar$          must end with 'bar'\n"
              << "    b[aoeiu]r     must have a vowel between 'b' and 'r'\n"
              << "    '^ab|^cd'     must begin with 'ab' or 'cd'\n"
              << "    [a-z]{16}     must contain letters only, no digits\n"
              << "    ^dusk.*dawn$  must begin with 'dusk' and end with 'dawn'\n"
              << "    [a-z2-7]{16}  any name - will succeed after one iteration\n";

    exit(0);
}