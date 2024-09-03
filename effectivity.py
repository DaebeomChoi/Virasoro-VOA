import itertools
import math
from scipy.optimize import linprog
import numpy as np

def gen(n):
    arr=[]
    for i in range(1,n+1):
        arr.append(i)
    result=[]
    for i in range(2, n-2):
        result.extend(list(itertools.combinations(arr,i)))
    return result

def halfgen(n):
    arr=[]
    even=[]
    for i in range(1,n+1):
        arr.append(i)
        if(i<n):
            even.append(i)
    result=[]
    if(n%2==0):
        for i in range(2, math.floor(n/2)):
            result.extend(list(itertools.combinations(arr,i)))
        result.extend(list(itertools.combinations(even, math.floor(n/2))))
    else:
        for i in range(2, math.floor(n/2)+1):
            result.extend(list(itertools.combinations(arr,i)))
    return result

def comp(list1,n):
    result=[]
    for i in range(1,n+1):
        if(not (i in list1)):
            result.append(i)
    return result

def rel(n):
    basis=halfgen(n)
    arr=[]
    for i in range(1,n+1):
        arr.append(i)
    vect=[]
    for pair in itertools.combinations(arr,4):
        rel1=[]
        rel2=[]
        for div in basis:
            if(((pair[0] in div) and (pair[1] in div) and (not (pair[2] in div))and (not (pair[3] in div))) or ((pair[2] in div) and (pair[3] in div) and (not (pair[0] in div))and (not (pair[1] in div)))):
                rel1.append(1)
            elif(((pair[0] in div) and (pair[2] in div) and (not (pair[1] in div))and (not (pair[3] in div))) or ((pair[1] in div) and (pair[3] in div) and (not (pair[0] in div))and (not (pair[2] in div)))):
                rel1.append(-1)
            else:
                rel1.append(0)
        vect.append(rel1)
        for div in basis:
            if(((pair[0] in div) and (pair[3] in div) and (not (pair[2] in div))and (not (pair[1] in div))) or ((pair[2] in div) and (pair[1] in div) and (not (pair[0] in div))and (not (pair[3] in div)))):
                rel2.append(1)
            elif(((pair[0] in div) and (pair[2] in div) and (not (pair[1] in div))and (not (pair[3] in div))) or ((pair[1] in div) and (pair[3] in div) and (not (pair[0] in div))and (not (pair[2] in div)))):
                rel2.append(-1)
            else:
                rel2.append(0)
        vect.append(rel2)
    return vect

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
k=10
rank=rank(11,k)
neg=[]
excep=[]
start=time.time()

for n in range(8,8):
    module=sumset(n,k)
    for config in module:
        check=0
        if(rank[tuple(config)]<2):
            continue
        if(config[0]>0):
            continue
        allbd=bdry(config)
        for bd in allbd:
            coeff=0
            for i in range(2,k+1):
                bd0=bd[0].copy()
                bd1=bd[1].copy()
                bd0[i-1]=bd[0][i-1]+1
                bd1[i-1]=bd[1][i-1]+1
                coeff+=cw(i,k)*rank[tuple(bd0)]*rank[tuple(bd1)]
            wt0=sum(bd[0])
            wt1=sum(bd[1])
            psi0=0
            psi1=0
            for i in range(2,k+1):
                psi0+=cw(i,k)*bd[0][i-1]
                psi1+=cw(i,k)*bd[1][i-1]
            psi=rank[tuple(config)]*(wt1*(wt1-1)*psi0+wt0*(wt0-1)*psi1)
            if(not ((n-1)*(n-2)*coeff<psi)):
                neg.append(config)
                break

end=time.time()
print(excep)
print(neg)

def modtolist(mod):
    l=len(mod)
    result=[]
    for i in range(0,l):
        result.extend([i+1]*mod[i])
    return result

def listtomod(list1,t):
    result=[]
    for i in range(1,t+1):
        result.append(list1.count(i))
    return result

def listdiv(list1, div,t):
    result=[0]*t
    for i in div:
        result[list1[i-1]-1]=result[list1[i-1]-1]+1
    return result

def cvdtodiv(mod,t):
    n=sum(mod)
    list1=modtolist(mod)
    basis=halfgen(n)
    result=[]
    for div in basis:
        i=len(div)
        coeff=0
        for j in range(1,n+1):
            if(j in div):
                coeff+=(n-i)*(n-i-1)*cw(list1[j-1],t)
            else:
                coeff+=i*(i-1)*cw(list1[j-1],t)
        coeff=coeff*rank[tuple(mod)]
        div2=comp(div,n)
        bd00=listdiv(list1, div, t)
        bd01=listdiv(list1, div2, t)
        for i in range(2,t+1):
            bd0=bd00.copy()
            bd1=bd01.copy()
            bd0[i-1]=bd00[i-1]+1
            bd1[i-1]=bd01[i-1]+1
            coeff-=cw(i,k)*rank[tuple(bd0)]*rank[tuple(bd1)]*(n-1)*(n-2)
        result.append(coeff)
    return result

def is_in_cone(v, vectors, rels):
    m = len(vectors)
    r = len(rels)
    vectors.extend(rels)

    A = np.column_stack(vectors)

    c = np.zeros(m+r)  # Coefficients to minimize
    bounds = [(0, None) for _ in range(m)]  # Coefficients must be non-negative
    bounds.extend([(None,None)]*r)
    res = linprog(c, A_eq=A, b_eq=v, bounds=bounds, method='highs')

    return res.success

def effect(mod, t):
    n=sum(mod)
    v=cvdtodiv(mod, t)
    basis=halfgen(n)
    vect=[]
    for div in basis:
        dum=[]
        for div2 in basis:
            if(div==div2):
                dum.append(1)
            else:
                dum.append(0)
        vect.append(dum)
    rels=rel(n)
    return is_in_cone(v, vect, rels)

counter=[]

print(effect([0,4,0,0,0,0,0,0,0,0],10))

for mod in neg:
    if(not effect(mod, k)):
        counter.append(mod)

print(counter)
