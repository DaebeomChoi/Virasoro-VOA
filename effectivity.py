import itertools
import math
import time
from sympy import symbols, Eq, linsolve, S, And
from sympy.solvers.inequalities import reduce_inequalities
from sympy import simplify
from fractions import Fraction
import copy
from z3 import *

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
def sumset(n, k):
    def backtrack(remaining, current, position):
        if position == k:
            if remaining == 0:
                result.append(current.copy())
            return

        for i in range(remaining + 1):
            current.append(i)
            backtrack(remaining - i, current, position + 1)
            current.pop()
    
    result = []
    backtrack(n, [], 0)
    return result

def modlist(n,t):
    list=sumset(n,t-1)
    result=[]
    for set in list:
        add=[0]
        add.extend(set)
        result.append(add)
    return result

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

#dividing modules into two sets, corresponds to boundaries, where one of them contains p points
def bdrypt(mod, p):
    k = len(mod)
    result = []
    current = []
    
    suffix_sum = [0] * (k + 1)
    for i in range(k - 1, -1, -1):
        suffix_sum[i] = suffix_sum[i + 1] + mod[i]
    
    def backtrack(index, remaining):
        if index == k:
            if remaining == 0:
                result.append(current.copy())
            return
        
        min_bi = max(0, remaining - suffix_sum[index + 1])
        max_bi = min(mod[index], remaining)
        
        for bi in range(min_bi, max_bi + 1):
            current.append(bi)
            backtrack(index + 1, remaining - bi)
            current.pop()
    
    backtrack(0, p)

    final=[]

    for list in result:
        rem=[]
        for i in range(0,k):
            rem.append(mod[i]-list[i])
        final.append([list,rem])

    return final

#conformal weight
def cw(i,k):
    return (i-1)*(2*k-i)

#generators and relations of the picard group via boundary divisors
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

#converting a set of modules to a divisor
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

#Checking effectivity with respect to relations


def effsum(v_vectors, w_vectors, target_vector):
    """
    Check if there exist positive integers c and a_i (for all i) and integers b_j (for all j)
    such that:
        c * target_vector = a_1*v_vectors[0] + ... + a_r*v_vectors[r-1] + b_1*w_vectors[0] + ... + b_s*w_vectors[s-1]
    
    Parameters:
        v_vectors: list of r vectors (each a list of m integers)
        w_vectors: list of s vectors (each a list of m integers)
        target_vector: list of m integers representing the target vector
    
    If a solution exists, the function prints the solution and verifies the equality by computing
    both the left-hand side and right-hand side.
    """
    m_dim = len(target_vector)   # dimension of the space
    r = len(v_vectors)           # number of v vectors
    s = len(w_vectors)           # number of w vectors

    solver = Solver()

    # Define the integer variables:
    #   c: positive integer multiplier for the target vector
    #   a_vars: list of positive integers corresponding to the v vectors
    #   b_vars: list of integers corresponding to the w vectors (can be any integer)
    c = Int('c')
    a_vars = [Int(f'a_{i}') for i in range(r)]
    b_vars = [Int(f'b_{j}') for j in range(s)]

    # Add constraints: c > 0 and each a_i > 0.
    solver.add(c > 0)
    for a in a_vars:
        solver.add(a > 0)

    # For each coordinate, add the constraint:
    #   c * target_vector[j] = sum_i (a_i * v_vectors[i][j]) + sum_j (b_j * w_vectors[j][j])
    for j in range(m_dim):
        lhs = c * target_vector[j]
        # Build the right-hand side as the sum of contributions from v_vectors and w_vectors.
        rhs_terms = [a_vars[i] * v_vectors[i][j] for i in range(r)] + \
                    [b_vars[jj] * w_vectors[jj][j] for jj in range(s)]
        rhs = Sum(rhs_terms)
        solver.add(lhs == rhs)

    # Check if the constraints are satisfiable.
    if solver.check() == sat:
        model = solver.model()
        print("Solution found:")
        sol_c = model[c]
        sol_a = [model[a] for a in a_vars]
        sol_b = [model[b] for b in b_vars]
        print("c =", sol_c) #erase this part if you don't want to see the full solution
        for i, a_val in enumerate(sol_a):
            print(f"a_{i} =", a_val)
        for j, b_val in enumerate(sol_b):
            print(f"b_{j} =", b_val)

        # Verification: compute both sides of the equation coordinate-wise as Python integers.
        left_side = [int(sol_c.as_long()) * target_vector[j] for j in range(m_dim)]
        right_side = []
        for j in range(m_dim):
            sum_val = 0
            for i in range(r):
                sum_val += int(sol_a[i].as_long()) * v_vectors[i][j]
            for jj in range(s):
                sum_val += int(sol_b[jj].as_long()) * w_vectors[jj][j]
            right_side.append(sum_val)
        
        print("\nVerification:") #erase this part if you don't want to see the verification process
        print("Left side (c * target_vector):", left_side)
        print("Right side (linear combination):", right_side)
        
        if left_side == right_side: # Only this part is essential
            print("Verification successful: The left and right sides match.") 
            return True
        else:
            print("Verification failed: The left and right sides do not match.")
    else:
        print("No solution exists.")
        return False

#Checking effectivity of conformal block divisors
k=9 #corresponds to \text{Vir}_{2,2k+1}
start=time.time()
rank=rank(2*k,k) #Dictionary for the fusion rule: the second slot corresponds to k as mentioned above, while the first slot represents the maximum number of modules.

print(time.time()-start)

for n in range(8,4*k-4): #number of modules
    #1st step: consider the standard form
    modnotwork=[] #set of modules such that the standard form does not works
    neg=[] #the standard form contains negative coefficients
    excep=[] #the standard form contains zero coefficients
    realfinal=[] #the set of conterexamples of conjecture 3.16
    module=modlist(n,k)
    for config in module:
        check=0
        if(rank[tuple(config)]<2): #this implies the divisor is zero
            continue
        level=0
        for i in range(1,k):
            level=level+i*config[i]
        if(level<2*k-1): #due to the proposition 3.31
            continue
        for p in range(2, min(math.floor(n/2)+1, k)):
            if((n-2)*(n-p)+1>(2*n-2-p)*(2*k-1-p)): #due to the theorem 3.13
                continue
            allbd=bdrypt(config,p)
            for bd in allbd:
                wt0=sum(bd[0])
                wt1=sum(bd[1])
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
                    check=1
                    neg.append([config, bd])
                if((n-1)*(n-2)*coeff==psi):
                    check=1
                    excep.append([config, bd])
        if(check==1):
            modnotwork.append(config)
    print(n)
    end=time.time()
    print(end-start) #you can erase undesired information here
    print(excep) 
    print(neg)
    print(modnotwork)

    #2nd step: Bruteforce for exceptional set of modules
    basis=halfgen(n)
    rels=rel(n)
    vect=[]
    for div in basis:
        dum=[]
        for div2 in basis:
            if(div==div2):
                dum.append(1)
            else:
                dum.append(0)
        vect.append(dum)
    finalexp=[]
    for mod in modnotwork:
        div=cvdtodiv(mod,k)
        feasible=effsum(vect, rels, div)
        if (not feasible):
            finalexp.append(mod)
    realfinal.extend(finalexp)
    print(n)
    end=time.time()
    print(end-start)
    print(finalexp) # the set of modules which is not contained in the interior of the cone generated by boundary divisors
    
    print(realfinal) #counterexamples of conjecture 3.16
