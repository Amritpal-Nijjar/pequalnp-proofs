/* Shared arithmetic for a single-threaded C control and an OpenCL GPU kernel. */
#if defined(__OPENCL_VERSION__) || defined(__OPENCL_C_VERSION__)
#define TABLE __constant
typedef uint word;
typedef uchar byte;
#else
#define TABLE const
typedef unsigned int word;
typedef unsigned char byte;
_Static_assert(sizeof(word) == 4, "This replay needs 32-bit unsigned integers");
#endif

static inline int can_finish(word *w, unsigned n, word target) {
    word subsets[20], supersets[20];
    unsigned small = 0, large = 0;
    for (unsigned i = 0; i < n; ++i) {
        const word v = w[i];
        if (v == target) return 1;
        if ((v & target) == v) subsets[small++] = v;
        if ((v & target) == target) supersets[large++] = v;
    }
    for (unsigned i = 0; i < n; ++i) {
        for (unsigned j = 0; j <= i; ++j) {
            const word left = w[i], right = w[j];
            for (unsigned op = 0; op < 2; ++op) {
                const word v = op ? (left | right) : (left & right);
                if (v == target) return 1;
                if ((v & target) == v) {
                    for (unsigned k = 0; k < small; ++k)
                        if ((v | subsets[k]) == target) return 1;
                }
                if ((v & target) == target) {
                    for (unsigned k = 0; k < large; ++k)
                        if ((v & supersets[k]) == target) return 1;
                }
            }
        }
    }
    return 0;
}

static inline byte check_index(TABLE word *bank, unsigned n, TABLE byte *pairs,
                               unsigned early, word index, word target) {
    word w[20];
    for (unsigned k = 0; k < n; ++k) w[k] = bank[k];
    for (unsigned k = 0; k < early; ++k) {
        const unsigned radix = n * (n + 1);
        const unsigned code = index % radix;
        index /= radix;
        const unsigned pair = (code / 2) * 2;
        const word a = w[pairs[pair]], b = w[pairs[pair + 1]];
        w[n++] = (code & 1) ? (a | b) : (a & b);
    }
    return (byte)can_finish(w, n, target);
}

#if defined(__OPENCL_VERSION__) || defined(__OPENCL_C_VERSION__)
#define BIT_COUNT(x) popcount(x)
#else
#define BIT_COUNT(x) __builtin_popcount(x)
#endif

static inline byte live_index(TABLE word *bank, unsigned n, TABLE byte *pairs,
                              unsigned early, word index, word upper, unsigned split,
                              word unpaid, word target) {
    word w[20];
    for (unsigned k = 0; k < n; ++k) w[k] = bank[k];
    for (unsigned k = 0; k < early; ++k) {
        if (k == split) index = upper;
        const unsigned radix = n*(n+1), code = index % radix;
        index /= radix;
        const unsigned pair = (code / 2) * 2;
        const unsigned a = pairs[pair], b = pairs[pair+1];
        unpaid = (unpaid & ~((1u<<a)|(1u<<b))) | (1u<<n);
        w[n] = (code & 1) ? (w[a] | w[b]) : (w[a] & w[b]);
        ++n;
        /* A later binary gate can reduce the number of live obligations by at
           most one, and the final output may leave one unpaid wire. */
        if (BIT_COUNT(unpaid) > early-k+2) return 0;
    }
    for (unsigned b = 0; b < n; ++b) {
        for (unsigned a = 0; a <= b; ++a) {
            const word previous = unpaid & ~((1u<<a)|(1u<<b));
            if (previous & (previous-1)) continue;
            for (unsigned op = 0; op < 2; ++op) {
                const word v = op ? (w[a]|w[b]) : (w[a]&w[b]);
                /* The last gate must read this penultimate output. Its other
                   input must pay any earlier wire that is still unused. */
                if (!previous && v == target) return 1;
                for (unsigned j = 0; j < n; ++j) {
                    if (previous && previous != (1u<<j)) continue;
                    if ((v & w[j]) == target || (v | w[j]) == target) return 1;
                }
            }
        }
    }
    return 0;
}

#if defined(__OPENCL_VERSION__) || defined(__OPENCL_C_VERSION__)
__kernel void replay(__constant word *bank, unsigned n, __constant byte *pairs,
                     unsigned early, word begin, word count, word target,
                     __global byte *flags) {
    const size_t i = get_global_id(0);
    if (i < count) flags[i] = check_index(bank, n, pairs, early, begin + (word)i, target);
}
__kernel void replay_live(__constant word *bank, unsigned n, __constant byte *pairs,
                          unsigned early, word begin, word upper, unsigned split, word unpaid,
                          word count, word target, __global byte *flags) {
    const size_t i = get_global_id(0);
    if (i < count) flags[i] = live_index(bank,n,pairs,early,begin+(word)i,upper,split,unpaid,target);
}
__kernel void count_live(__constant word *bank, unsigned n, __constant byte *pairs,
                         unsigned early, word begin, word upper, unsigned split, word unpaid,
                         word count, word target, volatile __global unsigned int *summary) {
    const size_t i = get_global_id(0);
    if (i < count && live_index(bank,n,pairs,early,begin+(word)i,upper,split,unpaid,target)) {
        atomic_inc(summary);
        atomic_min(summary+1,(unsigned)i);
    }
}
__kernel void late_banks(__constant word *records, __constant byte *pairs, unsigned count,
                         unsigned target, volatile __global unsigned int *summary) {
    const unsigned index = (unsigned)get_global_id(0);
    if (index >= count) return;
    const unsigned bank = index / 20592u, choice = index % 20592u;
    __constant word *record = records + bank * 12u;
    if (live_index(record, 11, pairs, 2, choice, 0, 2, record[11], target)) {
        atomic_inc(summary);
        atomic_min(summary + 1, index);
    }
}
#endif
