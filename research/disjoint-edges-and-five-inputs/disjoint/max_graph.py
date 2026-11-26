"""Upper bound the induced graph directly by the four physical raw masks."""
from itertools import combinations, combinations_with_replacement, product
from terms import literal,raw,values,pairs,all64
def check():
    both={};controls={}
    for pp in product(raw,repeat=4):
        a,b,c,d=pp
        if a>b or c>d:continue
        merged=tuple(sorted(((i,j) for i,j in combinations(range(3),2)
            if any(any((m>>(2*i+s)&1) and (m>>(2*j+s)&1) for s in (0,1)) for m in pp))))
        if merged not in both:
            forbid=[]
            for x in range(64):
                if any((x>>(2*i)&3)==3 for i in range(3)):continue
                if any((x>>(2*i)&3) and (x>>(2*j)&3) and (x>>(2*i)&3)!=(x>>(2*j)&3) and (i,j) not in merged for i,j in combinations(range(3),2)):continue
                forbid.append(x)
            both[merged]=[sum(1<<x for x in forbid if x.bit_count()<=k) for k in (1,2,3)]
        d0=values[a]&values[b]
        for x,y in product((0,1),repeat=2):
            d1=(values[c]|(d0 if x else 0)) & (values[d]|(d0 if y else 0))
            allterms=[d0&d1]+[v&t for v in (d0,d1) for t in literal]
            for k,neg in enumerate(both[merged],1):
                covered=0
                for h in allterms:
                    if not h&neg:covered|=h
                if all((covered>>(3<<(2*i)))&1 for i in range(3)):
                    controls[k]=controls.get(k,0)+1
    print('models by largest negative input size:',controls)
if __name__=='__main__':check()
