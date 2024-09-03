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

#Set of F-curves
def fcurves(mod):
    n=sum(mod)
    l=len(mod)
    dummy=[]
    for i in range(0,l):
        dummy.append([*range(0,mod[i]+1)])
    all=itertools.product(*dummy)
    flist=[]
    for br1 in all:
        tot=sum(br1)
        if(tot==0 or tot>n-3):
            continue
        rem1=[mod[i]-br1[i] for i in range(0,l)]
        dummy=[]
        for i in range(0,l):
            dummy.append([*range(0,rem1[i]+1)])
        all1=itertools.product(*dummy)
        for br2 in all1:
            tot=tot+sum(br2)
            if(sum(br2)==0 or tot>n-2):
                continue
            rem2=[rem1[i]-br2[i] for i in range(0,l)]
            dummy=[]
            for i in range(0,l):
                dummy.append([*range(0,rem2[i]+1)])
            all2=itertools.product(*dummy)
            for br3 in all2:
                tot=tot+sum(br3)
                if(sum(br3)==0 or tot>n-1):
                    continue
                br4=[rem2[i]-br3[i] for i in range(0,l)]
                flist.append([br1,br2,br3,br4])
    return flist

#Computing modules that occur
def appmod(br,k,rank):
    mod=[]
    for i in range(0,k):
        test=list(br)
        test[i]=br[i]+1
        if(rank[tuple(test)]>0):
            mod.extend([i]*rank[tuple(test)])
    return mod

#difference of virasoro conformal block divisors
l=7

nonample=[]
nonzero=[]
nonnef=[]

for n in range(5,10):
    rank1=rank(n,l-2)
    rank2=rank(n,l-1)
    config=sumset(n,l-2)
    for module in config:
        if(module[0]>0):
            continue
        check1=0
        check2=0
        check3=0
        level=0
        for i in range(0,l-2):
            level+=i*module[i]
        if(level<2*l-2 or 2*l+1<level):
            continue
        fcurve=fcurves(module)
        for curve in fcurve:
            check=0
            mod10=appmod(curve[0],l-2,rank1)
            mod11=appmod(curve[1],l-2,rank1)
            mod12=appmod(curve[2],l-2,rank1)
            mod13=appmod(curve[3],l-2,rank1)
            ncurve=[]
            for i in range(0,4):
                arr=list(curve[i])
                arr.append(0)
                ncurve.append(tuple(arr))
            mod20=appmod(ncurve[0],l-1,rank2)
            mod21=appmod(ncurve[1],l-1,rank2)
            mod22=appmod(ncurve[2],l-1,rank2)
            mod23=appmod(ncurve[3],l-1,rank2)
            totmod1=itertools.product(mod10,mod11,mod12,mod13)
            totmod2=itertools.product(mod20,mod21,mod22,mod23)
            for coll in totmod1:         
                pair=[]
                for i in range(0,l-2):
                    pair.append(coll.count(i))
                check=check+rank1[tuple(pair)]*(rank1[tuple(pair)]-1)
            for coll in totmod2:    
                pair=[]
                for i in range(0,l-1):
                    pair.append(coll.count(i))     
                check=check-rank2[tuple(pair)]*(rank2[tuple(pair)]-1)
            if(check==0):
                check1=1
                zero=curve
            elif(check>0):
                check2=1
                positive=curve
            else:
                check3=1
                negative=curve
        if(check1==1 and check2==1):
            nonample.append([module, zero, positive])
        if(check2==1):
            nonzero.append(module)
        if(check3==1):
            nonnef.append(module)
    print(n)

print(nonample)
print(nonnef)