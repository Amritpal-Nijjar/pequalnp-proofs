#include "suffix.cl"

__declspec(dllexport) void replay_batch(const word *bank, unsigned n, const byte *pairs,
                                       unsigned early, word begin, word count, word target,
                                       byte *flags) {
    for (word i = 0; i < count; ++i)
        flags[i] = check_index(bank, n, pairs, early, begin + i, target);
}

__declspec(dllexport) void live_batch(const word *bank, unsigned n, const byte *pairs,
                                     unsigned early, word begin, word upper, unsigned split,
                                     word unpaid, word count, word target, byte *flags) {
    for (word i = 0; i < count; ++i)
        flags[i] = live_index(bank,n,pairs,early,begin+i,upper,split,unpaid,target);
}
