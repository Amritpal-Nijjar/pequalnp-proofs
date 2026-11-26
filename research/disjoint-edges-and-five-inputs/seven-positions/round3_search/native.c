/* Independent CPU DFS. The pruning hypotheses are the Lean theorems in
   five_input_certificates.zip; the last two gates are tested directly. */
typedef unsigned int U;
typedef unsigned long long Q;
typedef unsigned char B;
static const U RAW[5]={0xaaaaaaaaU,0xccccccccU,0xf0f0f0f0U,0xff00ff00U,0xffff0000U};
static const U MASK[9]={0x55555555U,0xffff0000U,0x0000ffffU,0x33333333U,0xccccccccU,
                       0x0f0f0f0fU,0xf0f0f0f0U,0x00ff00ffU,0xff00ff00U};
static const U LIMIT[9]={2,2,3,4,4,4,4,4,4};
typedef struct {
    U w[15], normalized[15][9], gates[30];
    Q visits[10];
    U target, position, first, next, filtering, found;
    volatile U *stop;
} Search;

static U norm(U v,U mask){
    U left=v&mask, right=(~v)&mask;
    return left<right?left:right;
}
static void record(Search *s,U idx,U op,U a,U b){
    s->gates[3*idx]=op;s->gates[3*idx+1]=a;s->gates[3*idx+2]=b;
}
static U two(Search *s,U unpaid){
    if(__builtin_popcount(unpaid)>3) return 0;
    for(U a=0;a<13;a++){
        for(U b=a;b<13;b++){
            U rest=unpaid & ~((1U<<a)|(1U<<b));
            if(rest & (rest-1U))continue;
            U both[2]={s->w[a]&s->w[b],s->w[a]|s->w[b]};
            for(U op=0;op!=2;op++){
                U v=both[op];
                if((v&s->target)!=v && (v&s->target)!=s->target)continue;
                for(U p=0;p<=13;p++){
                    if(rest && rest!=(1U<<p))continue;
                    U h=p==13?v:s->w[p];
                    U f=(v&h)==s->target?0:(v|h)==s->target?1:2;
                    if(f==2)continue;
                    record(s,8,op,a,b);record(s,9,f,13,p);
                    return 1;
                }
            }
        }
    }
    return 0;
}
static void visit(Search *s,U depth,U unpaid,Q loss,U raw){
    if(s->found||*s->stop)return;
    s->visits[depth]++;
    if(depth==8){if(two(s,unpaid))s->found=1;return;}
    U n=5+depth;
    /* A remaining unary gate cannot reduce the number of unpaid wires. */
    if((U)__builtin_popcount(unpaid)>11U-depth-(s->position>=depth))return;
    if(depth==s->position){
        for(U a=5;a<n && !s->found;a++){
            s->w[n]=~s->w[a];
            for(U k=0;k<9;k++)s->normalized[n][k]=s->normalized[a][k];
            record(s,depth,2,a,a);
            visit(s,depth+1,(unpaid&~(1U<<a))|(1U<<n),loss,raw);
        }
        return;
    }
    U fixed=depth==0?s->first:(depth==(s->position==1?2U:1U)?s->next:0xffffffffU);
    for(U b=1;b<n;b++)for(U a=0;a<b;a++)for(U op=0;op<2;op++){
        if(fixed!=0xffffffffU && fixed!=b*(b+1)+2*a+op)continue;
        U v=op?(s->w[a]|s->w[b]):(s->w[a]&s->w[b]);
        Q next_loss=loss;
        U next_raw=raw;
        if(s->filtering){
            if(v==0 || v==~0U)continue;
            U fresh=1;
            for(U j=0;j<n;j++)if(v==s->w[j] || v==~s->w[j]){fresh=0;break;}
            if(!fresh)continue;
            if(a<5)next_raw+=1U<<(4*a);
            if(b<5)next_raw+=1U<<(4*b);
            if(next_raw&0x88888U)continue;
            for(U k=0;k<9;k++){
                U u=norm(v,MASK[k]), seen=(u==0);
                for(U j=0;j<n&&!seen;j++)seen=(s->normalized[j][k]==u);
                s->normalized[n][k]=u;
                next_loss+=(Q)seen<<(4*k);
                if(next_loss&0x888888888ULL)break;
            }
            if(next_loss&0x888888888ULL)continue;
        }
        s->w[n]=v;
        record(s,depth,op,a,b);
        visit(s,depth+1,(unpaid&~((1U<<a)|(1U<<b)))|(1U<<n),next_loss,next_raw);
        if(s->found||*s->stop)return;
    }
}
__declspec(dllexport) U search(U position,U first,U next,U target,U filtering,volatile U *stop,Q *visits,U *witness){
    Search s;
    s.target=target;s.position=position;s.first=first;s.next=next;s.filtering=filtering;s.found=0;s.stop=stop;
    for(U k=0;k<10;k++)s.visits[k]=0;
    Q loss=0;
    for(U k=0;k<9;k++)loss+=(Q)(7-LIMIT[k])<<(4*k);
    for(U i=0;i<5;i++){
        s.w[i]=RAW[i];
        for(U k=0;k<9;k++)s.normalized[i][k]=norm(RAW[i],MASK[k]);
    }
    visit(&s,0,0,loss,0x53335U);
    for(U k=0;k<10;k++)visits[k]=s.visits[k];
    if(s.found)for(U k=0;k<30;k++)witness[k]=s.gates[k];
    return s.found;
}
__declspec(dllexport) U endcheck(const U *bank,U owed,U wanted,U *witness){
    Search s;s.target=wanted;
    for(U i=0;i<13;i++)s.w[i]=bank[i];
    U hit=two(&s,owed);
    if(hit)for(U i=0;i<6;i++)witness[i]=s.gates[24+i];
    return hit;
}
