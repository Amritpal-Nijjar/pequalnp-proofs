/* Two remaining NOT positions in a ten-gate circuit with five raw inputs. */
static inline uint binary(uint left, uint right, uint op) {
    return op ? left | right : left & right;
}

static inline uint append_gate(__private uint *w, uint at, uint code,
                               __constant uchar *pairs, uint debt) {
    const uint offset = code & ~1u;
    const uint a=pairs[offset], b=pairs[offset + 1];
    w[at] = binary(w[a],w[b],code & 1u);
    return (debt & ~((1u<<a)|(1u<<b))) | (1u<<at);
}

static inline uint last_pair(__private uint *w, uint owed, uint wanted) {
    if (popcount(owed) > 3u) return 0;
    for (uint b=0;b<13;b++) {
        const uint without_b=owed & ~(1u << b);
        if (popcount(without_b) > 2u) continue;
        for (uint a=0;a<=b;a++) {
            const uint rest=without_b & ~(1u << a);
            if (rest & (rest-1u)) continue;
            for (uint gate=0;gate<2;gate++) {
                const uint v=binary(w[a],w[b],gate);
                const uint common=v & wanted;
                if (common != v && common != wanted) continue;
                if (rest) {
                    const uint other=w[31u-clz(rest)];
                    if ((v&other)==wanted || (v|other)==wanted) return 1;
                } else {
                    if (v==wanted) return 1;
                    for (uint j=0;j<13;j++)
                        if ((v&w[j])==wanted || (v|w[j])==wanted) return 1;
                }
            }
        }
    }
    return 0;
}

__kernel void search_placement(__constant uint *records, __constant uchar *pairs,
                               uint position, uint begin, uint count, uint target,
                               volatile __global uint *hits) {
    const uint i=(uint)get_global_id(0);
    if(i>=count) return;
    const uint idx=i+begin;
    const uint stride=position==6u ? 102960u : 101640u;
    const uint root=idx/stride, local_index=idx%stride;
    __constant uint *record=records+11u*root;
    uint w[13];
    for(uint j=0;j<10;j++) w[j]=record[j];
    uint unpaid=record[10];
    const uint first=(position==6u) ? local_index/936u : local_index/924u;
    unpaid=append_gate(w,10,first,pairs,unpaid);
    if(position==6u){
        const uint inv=5u+((local_index/156u)%6u);
        w[11]=~w[inv];
        unpaid=(unpaid & ~(1u<<inv)) | (1u<<11);
        unpaid=append_gate(w,12,local_index%156u,pairs,unpaid);
    }else{
        unpaid=append_gate(w,11,(local_index/7u)%132u,pairs,unpaid);
        const uint inv=5u+local_index%7u;
        w[12]=~w[inv];
        unpaid=(unpaid & ~(1u<<inv)) | (1u<<12);
    }
    if(last_pair(w,unpaid,target)){
        atomic_inc(hits);
        atomic_min(hits+1,i);
    }
}
