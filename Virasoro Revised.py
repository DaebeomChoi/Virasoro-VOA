import itertools
import math
import time

#Dictionary for the Fusion Rule
def fuslist(t):
    fusion={}
    for p in range(1,t+1):
        for q in range(1,t+1):
            list=[]
            for i in range(1, min(p,q)+1):
                if(abs(p-q)+2*i-1<t+1):
                    list.append(abs(p-q)+2*i-1)
                else:
                    list.append(2*t-abs(p-q)-2*i+2)
            fusion[(p,q)]=list
    return fusion

#Set of t numbers whose sum is n
def sumset(n,t):
    if(n==0):
        return [[0]*t]
    elif(t==1):
        return [[n]]
    else:
        mlist=[]
        for i in range(0, n+1):
            for slist in sumset(n-i,t-1):
                slist.append(i)
                mlist.append(slist)
        return mlist

#Find the positions with positive value
def posval(list):
    l=len(list)
    check=0
    pos=[]
    for i in range(0,l):
        if(list[i]>0):
            pos.append(i)
            if(check==0):
                check=1
            else:
                break
    return pos

#Rank of conformal blocks
def rank(n,t):
    rank={}
    base=[0]*t
    rank[tuple(base)]=1
    base=[1]
    base.extend([0]*(t-1))
    rank[tuple(base)]=1
    for i in range(2,t+1):
        base=[]
        for j in range(1,t+1):
            if(i==j):
                base.append(1)
            else:
                base.append(0)
        rank[tuple(base)]=0
    fusion=fuslist(t)
    for m in range(2,n+1):
        config=sumset(m,t)
        for module in config:
            if(module[0]>0):
                omodule=tuple(module)
                module[0]=0
                nmodule=tuple(module)
                a=rank[nmodule]
                rank[omodule]=a
            elif(module[posval(module)[0]]>1):
                mlist=fusion[(posval(module)[0]+1, posval(module)[0]+1)]
                nmodule=module.copy()
                nmodule[posval(module)[0]]=module[posval(module)[0]]-2
                rk=0
                for elt in mlist:
                    nmoduledum=nmodule.copy()
                    nmoduledum[elt-1]=nmodule[elt-1]+1
                    rk=rk+rank[tuple(nmoduledum)]
                rank[tuple(module)]=rk
            else:
                mlist=fusion[(posval(module)[0]+1, posval(module)[1]+1)]
                nmodule=module.copy()
                nmodule[posval(module)[0]]=module[posval(module)[0]]-1
                nmodule[posval(module)[1]]=module[posval(module)[1]]-1
                rk=0
                for elt in mlist:
                    nmoduledum=nmodule.copy()
                    nmoduledum[elt-1]=nmodule[elt-1]+1
                    rk=rk+rank[tuple(nmoduledum)]
                rank[tuple(module)]=rk
    return rank

#dividing modules into two sets, corresponds to boundaries
def bdry(mod):
    n=sum(mod)
    l=len(mod)
    dummy=[[*range(0,math.floor(mod[0]/2)+1)]]
    for i in range(1,l):
        dummy.append([*range(0,mod[i]+1)])
    all=itertools.product(*dummy)
    corr=[]
    for bd in all:
        if(sum(bd)>1 and n-1>sum(bd)):
            bdres=[]
            for i in range(0,l):
                bdres.append(mod[i]-bd[i])
            corr.append([list(bd), bdres])
    return corr

#conformal weight
def cw(i,k):
    return (i-1)*(2*k-i)

#Checking effectivity of conformal block divisors
k=8
start=time.time()
rank=rank(4*k-6,k)
neg=[]
excep=[]


for n in range(6,4*k-5):
    module=sumset(n,k)
    for config in module:
        if(config[0]>0):
            continue
        if(rank[tuple(config)]<2):
            continue
        level=0
        for i in range(1,k):
            level=level+i*config[i]
        if(level<2*k-1):
            continue
        allbd=bdry(config)
        for bd in allbd:
            wt0=sum(bd[0])
            wt1=sum(bd[1])
            pt=min(wt0, wt1)
            if(pt>k-1):
                continue
            if((n-2)*(n-pt)+1>(2*n-2-pt)*(2*k-1-pt)):
                continue
            coeff=0
            for i in range(2,k+1):
                bd0=bd[0].copy()
                bd1=bd[1].copy()
                bd0[i-1]=bd[0][i-1]+1
                bd1[i-1]=bd[1][i-1]+1
                coeff+=cw(i,k)*rank[tuple(bd0)]*rank[tuple(bd1)]
            psi0=0
            psi1=0
            for i in range(2,k+1):
                psi0+=cw(i,k)*bd[0][i-1]
                psi1+=cw(i,k)*bd[1][i-1]
            psi=rank[tuple(config)]*(wt1*(wt1-1)*psi0+wt0*(wt0-1)*psi1)
            if((n-1)*(n-2)*coeff>psi):
                neg.append([config, bd])
            if((n-1)*(n-2)*coeff==psi):
                excep.append([config, bd])
    print(n)
    end=time.time()
    print(end-start)
    print(excep)
    print(neg)
