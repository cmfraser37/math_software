from sage.combinat import *




#This is hard-coded to do a particular calculation of the 
#all perms u such that P_{u;T} is the standard monomial F such that 
# ch(T'\cup T') = ch(T')^2-F, where T is the nonreal tableau with columns [1,2,5],[3,6,8],[4,7,9]
def CreateSingleKLFile():
    Asciilist = ['0','1','2','3','4','5','6','7','8','9',':',';','<','=','>','?']
    print Asciilist
    AllUs = [Permutation(list(a)+list(b)+list(c)+list(d)+list(e)+list(f)) for a in Permutations([2,6]) for b in Permutations([1,4,9,10]) for c in Permutations([3,5,13,14]) for d in Permutations([8,16]) for e in Permutations([7,12]) for f in Permutations([11,15])]
    A = [1,1,2,2,3,3,4,4,4,4,5,5,5,5,6,6]
    Bsorted = [3,3,4,4,4,4,5,5,5,5,6,6,7,7,8,8]
    B = [3,3,4,4,4,4,5,5,5,5,7,7,6,6,8,8]
    k = len(A)
    print k
    assert k== len(B)
    u = AllUs[0]
    SWeWant = sorted([(A[u[i]-1],Bsorted[i]) for i in range(k)])
    for u in AllUs:
        assert sorted([(A[u[i]-1],Bsorted[i]) for i in range(k)]) == SWeWant            
    STopTerm = sorted([(A[i],B[i]) for i in range(k)])            
    w = Permutation([2,1,6,5,4,3,10,9,8,7,14,13,12,11,16,15])
    assert sorted([(A[w[i]-1],Bsorted[i]) for i in range(k)]) == STopTerm
    print STopTerm
    w0 = Permutation([16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1])
    #w = s[1]*s[3]*s[4]*s[5]*s[3]*s[4]*s[3]*s[7]*s[8]*s[9]*s[7]*s[8]*s[7]*s[11]*s[12]*s[13]*s[11]*s[12]*s[11]*s[15]
    y = str().join([Asciilist[int(x)-1] for x in w*w0])
    f = file('singleuuu.txt','w')
    for u in AllUs:
        f.write(str().join([Asciilist[int(x)-1] for x in u*w0])+' '+y+'\n')
    f.close()

def MassageSingleKLFile():
    w = Permutation([2,1,6,5,4,3,10,9,8,7,14,13,12,11,16,15])
    w0 = Permutation([16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1])
    ylen = w.length()
    print w,w0,ylen
    uctr = 0
    tabcoeff = 0        
    us = [Permutation(list(a)+list(b)+list(c)+list(d)+list(e)+list(f)) for a in Permutations([2,6]) for b in Permutations([1,4,9,10]) for c in Permutations([3,5,13,14]) for d in Permutations([8,16]) for e in Permutations([7,12]) for f in Permutations([11,15])]    
    with open('resultuuu.txt','r') as f: L = [l.strip() for l in f]
    print "number of coefficients is ", len(L)
    print len(us), len(L)
    uctr = 0
    for l in L: #l is the output of Greg's program corresponding to a permutation that yields tab
        sgn = (-1)**(us[uctr].length()+ylen)
        uctr+=1
        suffix = l[max([x for x in range(len(l)) if l[x] == ' '])+1:].split(',')    #suffix is the sequence of KL coefficients for the KL poly determined by l
        #print "tab ", tab,"suffix", suffix, "sum ", sum([int(x) for x in suffix])
        tabcoeff += sgn*sum([int(x) for x in suffix])
        if sum([int(x) for x in suffix]):
            print uctr, suffix, "the coefficient was ", tabcoeff       
    return tabcoeff
    
    

    



#only wrote this for 3by3 immanants so far
def KLImmanant():
    P = PolynomialRing(ZZ,['a','b','c','d','e','f','g','h','i'])
    print P
    a,b,c,d,e,f,g,h,i = P.gens()
    M = matrix(P,3,3,[d,d*h,d*h*i,b*d,b*d*h+e,b*d*h*i+e*g+e*i,a*b*d,a*b*d*h+a*e+c*e,a*b*d*h*i+(a+c)*e*(g+i)+f])
    #M = matrix(P,3,3,[a,b,c,d,e,f,g,h,i])
    W = WeylGroup('A2', prefix = 's')
    q = LaurentPolynomialRing(QQ,'q').gens()[0]
    KL = KazhdanLusztigPolynomial(W,q)
    w0=W.long_element()
    s = W.simple_reflections()
    w = s[1]    
    output = 0*a
    for u in list(W):
        ustr = u.inverse().to_permutation_string()
        outputcoeff =(-1)**((u*w).length())*KL.P(u*w0, w*w0)(1)
        transversal = M[0][int(ustr[0])-1]*M[1][int(ustr[1])-1]*M[2][int(ustr[2])-1]
        output+= outputcoeff*transversal
    return output



#input T should be a  list of Plucker indices, e.g. [1,3,4]    
#returns a symbolic polynomial in the n by m matrix entries
def PluckerFromColumn(Plu,m):
    n = len(Plu)
    R = PolynomialRing(QQ,n*m,['x'+str(i)+str(j) for i in range(1,n+1) for j in range(1,m+1)])
    Xs = R.gens()
    output = 0*Xs[0]
    for p in Permutations(n):
        ss = p.sign()
        nextterm = ss*R.one()
        for i in range(n):
            nextterm *= Xs[(p[i]-1)*m+Plu[i]-1]
        output += nextterm
    return output

    
#input T should be a  list of lists of  Plucker indices, e.g. [[1,3,4],[2,5,6]]
#returns the corresponding P_T
#m is Gr(n,m)
def PluckerFromTableau(T,m):
    #print "doing PluFromTab ", T 
    PsubT = PluckerFromColumn(T[0],m)
    for t in T[1:]:
        PsubT*= PluckerFromColumn(t,m)
    return PsubT

#input T should be a  list of lists of  Plucker indices with the ncols m; m is Gr(n,m)   
#returns P_T evaluated on a 4\times 8 matrix M which is hard-coded, but can whose entries can be changed directly. 
def NPluckerFromTableau(T):
    M = matrix(ZZ,[[0,-2,5,0,-3,0,2,-1],[0,-3,-7,5,0,6,1,4],[-2,0,5,-1,0,5,2,0],[11,3,0,1,-3,-4,6,7]])
    #print "doing PluFromTab ", T 
    PsubT = M.matrix_from_columns([x-1 for x in T[0]]).determinant()
    for t in T[1:]:
        PsubT*= M.matrix_from_columns([x-1 for x in t]).determinant()
    return PsubT



    
    
    
#input  should be a  list of starting points A and gaps B, with the gaps permuted in the order that they appear in T
def LongestPerm(A,Bsorted,B):
    k = len(A)
    S = set([(A[i],B[i]) for i in range(k)])
    W = WeylGroup('A'+str(k-1), prefix = 's')
    print "warning: doing hard-coded"
    s = W.simple_reflections()
    return s[1]*s[2]*s[1]*s[4]*s[5]*s[4]*s[7]*s[8]*s[7]*s[10]*s[11]*s[10]
    winner = W.one()
    for w in W:
        wstr = w.inverse().to_permutation_string()
        if set([(A[int(wstr[i])-1],Bsorted[i]) for i in range(k)]) == S:   ##### using set is buggy; need to use multisets!!!
            #print wstr
            if w.length()>winner.length():
                winner = w
    return winner


#directly compute chT on the matrix M; only works for 4 \times 8 matrices at the moment. 
def NChT(A,B,n):
    output = 0*QQ.one()
    k = len(A)
    if k==1:
        return output
    W = WeylGroup('A'+str(k-1), prefix = 's')
    q = LaurentPolynomialRing(QQ,'q').gens()[0]
    KL = KazhdanLusztigPolynomial(W,q)
    w0=W.long_element()
    s = W.simple_reflections()
    Bsorted = [int(x) for x in B]
    Bsorted.sort()
    w = LongestPerm(A,Bsorted,B)
    print "longest perm in the double coset is ", w
    noncontributers = []
    noninsiders = []
    uctr = 0    
    for u in list(W):
        uctr+=1
        ustr = u.inverse().to_permutation_string()
        T = []
        uflag = 1
        for i in range(k):
            if range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1).count(Bsorted[i]):
                T.append([x for x in range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1) if x != Bsorted[i]])
            else:
                noninsiders.append(ustr)
                uflag = 0            
                break
        if uflag:
            t2=KL.P(u*w0, w*w0)
            t2*=(-1)**((u*w).length())
            if t2(1) ==0:
                noncontributers.append(ustr)
                continue                
            output += t2(1)*NPluckerFromTableau(T)
    return output


# 135 246 is 134 235 245 346 so A = 3221 B = 5432
# 16 wedge 23 wedge 45 wedge  is 145 236-123 456

#input A is a list of starting points A and gaps B
#n is the number of rows
#m is the size of the maximal entry

#this version computes  ChT as a poly in k by n matrix entries using Sage to compute the KL values


# to check that u vs u.inverse convention is correct, test Ch([1,1,1,2],[2,2,3,3]). it should coincide with Delta[234,145,134,124] and it only does with the inverse convention. 

#directly compute chT as a polynomial in n\times m matrix entries; getting KL values in Sage is slow so this only works for small tableaux
def ChTMatrixEntries(A,B,n,m):
    output = PluckerFromColumn([x for x in range(A[0],A[0]+n+1) if x != B[0]],m)
    k = len(A)
    if k==1:
        return output
    output*=0                
    W = WeylGroup('A'+str(k-1), prefix = 's')
    q = LaurentPolynomialRing(QQ,'q').gens()[0]
    KL = KazhdanLusztigPolynomial(W,q)
    w0=W.long_element()
    s = W.simple_reflections()
    Bsorted = [int(x) for x in B]
    Bsorted.sort()
    w = LongestPerm(A,Bsorted,B)
    #w = s[2]*s[4]*s[6]
    print "longest perm in the double coset is ", w
    noncontributers = []
    noninsiders = []
    uctr = 0    
    for u in list(W):
        uctr+=1
        #print "u", u
        ustr = u.inverse().to_permutation_string()
        T = []
        uflag = 1
        for i in range(k):
            if range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1).count(Bsorted[i]):
                T.append([x for x in range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1) if x != Bsorted[i]])
            else:
                #print "this perm didn't fit inside"
                noninsiders.append(ustr)
                uflag = 0            
                break
        if uflag:
            t2=KL.P(u*w0, w*w0)
            t2*=(-1)**((u*w).length())
            if t2(1) ==0:
                noncontributers.append(ustr)
                #print "KL of zero"
                continue                
            #print "KLPoly is ", t2, "tableau is ", T
            output += t2(1)*PluckerFromTableau(T,m)
    #print "KL vanished ", noncontributers
    #print "too small ", noninsiders
    return output

    
    
    
# this version creates the standard monomial expansion of chT by creating a dictionary 
# {tableau: coefficient} using Sage to compute KL values. Unlike ChTMatrixEntries, it does not compute the polynomial in matrix entries. 
#This dictionary could  be used to write down a symbolic expression for the standard monomial expression. 
def ChTDictionary(A,B,n,m):
    k = len(A)
    if k==1:
        return "method not made yet"
    W = WeylGroup('A'+str(k-1), prefix = 's')
    q = LaurentPolynomialRing(QQ,'q').gens()[0]
    KL = KazhdanLusztigPolynomial(W,q)
    w0=W.long_element()
    s = W.simple_reflections()
    Bsorted = [int(x) for x in B]
    Bsorted.sort()
    w = LongestPerm(A,Bsorted,B)    
    print "longest perm is ", w
    noncontributers = []
    noninsiders = []
    TabCoeffs = {}
    uctr = 0    
    for u in list(W):
        uctr+=1
        #print "u", u
        ustr = u.inverse().to_permutation_string()   ### we double checked the conventions above
        T = []
        uflag = 1
        for i in range(k):
            if range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1).count(Bsorted[i]):
                T.append([x for x in range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1) if x != Bsorted[i]])
            else:
                #print "this perm didn't fit inside"
                noninsiders.append(ustr)
                uflag = 0            
                break
        if uflag:
            #print "starting KL computation"
            t2=KL.P(u*w0, w*w0)(1)
            t2*=(-1)**((u*w).length())
            #print "ending KL computation"
            if t2 ==0:
                #print "no contribution from KL ", ustr
                noncontributers.append(ustr)
                continue                
            print "contributing u is ", ustr, "KLPoly is ", t2, "tableau is ", T
            Tseq, TtoStr = [[x[0],x[1],x[2]] for x in T],''
            Tseq.sort()
            for x in Tseq:
                TtoStr+= str(x[0])+str(x[1])+str(x[2])+', '
            if TabCoeffs.has_key(TtoStr) and len(TtoStr):
                currentcoeff = TabCoeffs[TtoStr]
                TabCoeffs.update({TtoStr:currentcoeff+t2})
            else:
                TabCoeffs.update({TtoStr:t2})            
    return TabCoeffs
 

# this version creates a dictionary {tableaux T: set of perms u such that u \cdot T' = T}. One can translate such a dictionary into a file that Greg's code can run on
def ChTSupport(A,B,n,m):
    k = len(A)
    if k==1:
        return "method not made yet"
    W = WeylGroup('A'+str(k-1), prefix = 's')
    s = W.simple_reflections()
    Bsorted = [int(x) for x in B]
    Bsorted.sort()    ### Bsorted is related to lambda in the notation of our paper; A is related to mu in the notation of our paper
    print "sorted", Bsorted
    w = LongestPerm(A,Bsorted,B)
    print "found w", w,W
    print w.inverse().to_permutation_string()
    TabCoeffs = {}
    uctr = 0
    for u in list(W):
        uctr+=1
        ustr = u.inverse().to_permutation_string()    ##### we double checked u vs uinv conventions above
        T = []
        uflag = 1
        for i in range(k):
            if range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1).count(Bsorted[i]):
                T.append([x for x in range(A[int(ustr[i])-1],A[int(ustr[i])-1]+n+1) if x != Bsorted[i]])
            else:
                uflag = 0            
                break
        if uflag:
            Tseq, TtoStr = [[str(y) for y in x] for x in T],''
            Tseq.sort()
            for x in Tseq:
                TtoStr+= str().join(x)+', '
            if TabCoeffs.has_key(TtoStr) and len(TtoStr):
                TabCoeffs[TtoStr].add(u)
            else:
                TabCoeffs[TtoStr] = {u}
    return (TabCoeffs,w)
    

    
# TabCoeffs is tableaux with the u's that permute it appropriately
# TabValues is tableaux with the sum of the Kazhdan Lusztig values    
    
    
    
#take in a dictionary from tableaux to sets of permutations; pop out a bunch of .txt files, each of which contains pairs of permutations to be run in Greg's program    
def CreateKLFiles(tabcoeffscopy,w):
    Asciilist = ['0','1','2','3','4','5','6','7','8','9',':',';','<','=','>','?']
    print "creating ", len(tabcoeffscopy.keys()), " files for Greg's program"
    W = w.parent()
    s = W.simple_reflections()
    w0=W.long_element()
    print "using this w", w, "in Weyl group ", W 
    y = str().join([Asciilist[int(x)-1] for x in (w*w0).inverse().to_permutation_string()])
    ictr = 0    
    for tab in tabcoeffscopy.keys():    
        f = file('tab'+str(ictr)+'.txt','w')
        ictr +=1
        us = [u for u in tabcoeffscopy[tab]]
        for u in us:
            f.write(str().join([Asciilist[int(x)-1] for x in (u*w0).inverse().to_permutation_string()])+' '+y+'\n')
        f.close()
        
# take in .txt output of Greg's program and create a dictionary Tableaux: coefficients. This is a workaround to doing ChTDictionary in Sage
def MassageKLFiles(tabcoeffscopy,w):
    W = w.parent()
    s = W.simple_reflections()
    w0=W.long_element()
    ylen = w.length()
    ictr = 0
    TabWithCoeff = {}
    print w,w0,W,ylen
    for tab in tabcoeffscopy.keys():
        #print "summing up the ", len(tabcoeffscopy[tab]), " KL coefficients for this tab ", tab, "file number " ,ictr
        us = [u for u in tabcoeffscopy[tab]]
        uctr = 0
        tabcoeff = 0        
        with open('result'+str(ictr)+'.txt','r') as f: L = [l.strip() for l in f]
        ictr +=1
        assert len(us) == len(L)
        #print "list L from file", L
        for l in L:                #l is the output of Greg's program corresponding to a permutation that yields tab
            sgn = (-1)**(us[uctr].length()+ylen)
            uctr+=1
            suffix = l[max([x for x in range(len(l)) if l[x] == ' '])+1:].split(',')    #suffix is the sequence of KL coefficients for the KL poly determined by l
            #print "tab ", tab,"suffix", suffix, "sum ", sum([int(x) for x in suffix])
            tabcoeff += sgn*sum([int(x) for x in suffix])
        #print "the coefficient was ", tabcoeff
        TabWithCoeff[tab] = tabcoeff
    return TabWithCoeff

# Given a dictionary as created in MassageKlFiles; create the poly in k \times n matrix entries
def TurnDictionaryIntoPolynomial(tabwithcoeff,m):
    T = tabwithcoeff
    tabsum = 0
    for tab in [t for t in T.keys() if T[t]]:
        tabcopy = tab.split(', ')[:-1]
        tabL = []
        for t in tabcopy:
            tabL.append([int(x) for x in t])
        print tab,tabL
        tabsum += T[tab]*PluckerFromTableau(tabL,m)
        print(len(tabsum.coefficients()))
    return tabsum

# Given a dictionary as created in MassageKlFiles; numerically evaluate Ch(T) on a fixed  k \times n matrix hard-coded above. At the moment only works for 4\times 8
def TurnDictionaryIntoN(tabwithcoeff):
    T = tabwithcoeff
    tabsum = 0*QQ.one()
    print len(T.keys()),len([t for t in T.keys() if T[t]])
    for tab in [t for t in T.keys() if T[t]]:
        tabcopy = tab.split(', ')[:-1]
        tabL = []
        for t in tabcopy:
            tabL.append([int(x) for x in t])
        tabsum += T[tab]*NPluckerFromTableau(tabL)
        print tab,tabsum        
    return tabsum


    
####################### Check directly that Ch(T) = Web(T) for small nonreal tableau T
# Web T1 is the SL3 tableau with cols 125,368,479; it is the single cycle web with forks 23,56,89
# A is 12344556
# B is 34455768
# w_T is s2*s4*s6
def CheckSL3WebT1(tester):
    F = PluckerFromTableau([[2,3,4],[4,5,6],[5,6,7],[5,6,7],[6,7,8]],9)
    A = PluckerFromTableau([[1,4,5],[2,7,8],[3,6,9]],9)
    B = PluckerFromTableau([[2,4,5],[1,7,8],[3,6,9]],9)
    C = PluckerFromTableau([[1,2,3],[4,5,6],[7,8,9]],9)
    D = PluckerFromTableau([[1,2,9],[3,4,5],[6,7,8]],9)
    H = PluckerFromTableau([[1,2,6],[3,7,8],[4,5,9]],9)-PluckerFromTableau([[1,2,6],[3,4,5],[7,8,9]],9)-PluckerFromTableau([[1,2,3],[6,7,8],[4,5,9]],9)-PluckerFromTableau([[1,2,9],[3,7,8],[4,5,6]],9)
    assert H == A-B-C-D
    return tester == F*(A-B-C-D) 
    
# Web T2 is the SL3 tableau with cols 136,247,589; it is the single cycle web with forks 12,45,78
# A is 12233456
# B is 24355667
# wT is s2*s4*s6 
def CheckSL3WebT2(tester):
    F = PluckerFromTableau([[2,3,4],[3,4,5],[3,4,5],[4,5,6],[6,7,8]],9)
    A = PluckerFromTableau([[2,5,6],[3,8,9],[1,4,7]],9)
    B = PluckerFromTableau([[3,5,6],[2,8,9],[1,4,7]],9)
    C = PluckerFromTableau([[2,3,4],[5,6,7],[1,8,9]],9)
    D = PluckerFromTableau([[1,2,3],[4,5,6],[7,8,9]],9)    
    assert tester == F*(A-B-C-D)


    
# Web T4 is the SL4 tableau with cols [[1,2,4,6],[3,5,7,8]] ; it is the SL4 single cycle web with forks 12,34,56,78
# A is [1,2,3,4]
# B is [3,5,4,6]
#             
def CheckSL4WebT4(tester):
    F = PluckerFromTableau([[2,3,4,5],[4,5,6,7]],8)
    A = PluckerFromTableau([[1,2,4,7],[3,5,6,8]],8)
    B = PluckerFromTableau([[1,2,3,7],[4,5,6,8]],8)
    C = PluckerFromTableau([[1,2,4,8],[3,5,6,7]],8)
    D = PluckerFromTableau([[1,2,3,8],[4,5,6,7]],8)
    assert tester == F*(A-B-C+D)

    
# Web T5 is the SL4 tableau with cols [[1,3,5,7],[2,4,6,8]]; it is the SL4 single cycle web with forks 23,45,67,18
# A is [1,2,2,3,3,4]
# B is [2,4,3,6,5,7]
# w is s2*s4      
# I only checked this one numerically because the polys are large and I was lazy, but a symbolic check *is* doable in this case
def CheckSL4WebT5(tester):
    F = NPluckerFromTableau([[2,3,4,5],[3,4,5,6],[3,4,5,6],[4,5,6,7]])
    A = NPluckerFromTableau([[2,3,5,8],[1,4,6,7]])
    B = NPluckerFromTableau([[2,3,4,8],[1,5,6,7]])
    C = NPluckerFromTableau([[1,2,3,5],[4,6,7,8]])
    D = NPluckerFromTableau([[1,2,3,4],[5,6,7,8]])
    #print tester-F*(A-B-C+D)
    assert tester==F*(A-B-C+D)
    print tester,F*(A-B-C+D)
    
    

# Tableau T_4^2 with cols [1,2,4,6]^2,[3,5,7,8]^2 
# A is [1,1,2,2,3,3,4,4] B is [3,3,5,5,4,4,6,6]
# w is s7*s3*s4*s5*s3*s4*s3*s1   
# frozen that divides is  2345^2,4567^2   
def CheckSL4WebT4T4(tester):
    F = NPluckerFromTableau([[2,3,4,5],[4,5,6,7]])
    A = NPluckerFromTableau([[1,2,4,7],[3,5,6,8]])
    B = NPluckerFromTableau([[1,2,3,7],[4,5,6,8]])
    C = NPluckerFromTableau([[1,2,4,8],[3,5,6,7]])
    D = NPluckerFromTableau([[1,2,3,8],[4,5,6,7]])
    E = NPluckerFromTableau([[1,2,3,4],[3,4,5,6],[5,6,7,8],[1,2,7,8]])
    assert tester == (F*(A-B-C+D))**2-F**2*E

# Tableau T_4^3 with cols [1,2,4,6]^3,[3,5,7,8]^3 
# A is [1,1,1,2,2,2,3,3,3,4,4,4] B is [3,3,3,5,5,5,4,4,4,6,6,6]
# w is 321654987121110 in one-line notation, or 
# s1*s2*s1*s4*s5*s4*s7*s8*s7*s10*s11*s10 as a reduced word.   
# frozen that divides is  2345^3,4567^3   
def CheckSL4WebT4T4T4(tester):
    F = NPluckerFromTableau([[2,3,4,5],[4,5,6,7]])
    A = NPluckerFromTableau([[1,2,4,7],[3,5,6,8]])
    B = NPluckerFromTableau([[1,2,3,7],[4,5,6,8]])
    C = NPluckerFromTableau([[1,2,4,8],[3,5,6,7]])
    D = NPluckerFromTableau([[1,2,3,8],[4,5,6,7]])
    E = NPluckerFromTableau([[1,2,3,4],[3,4,5,6],[5,6,7,8],[1,2,7,8]])
    assert tester == (F*(A-B-C+D))**2-F**2*E

    

    
    

            
            
                    
#T is input as a list of its columns    
def GapWidth(T):
    #print T,T[0]
    nrows = len(T[0])
    return sum([t[-1:][0]-t[0]-nrows+1 for t in T])
            

#T is input as a list of its rows
def GapWidthRowInput(T):
    TTranspose = []
    for i in range(len(T[0])):
        nextrow = []
        for t in T:
            nextrow.append(t[i])
        TTranspose.append(nextrow)
    return GapWidth(TTranspose)        
        
    

        
    
    
    
    
        

        
    
    










##################### junk at this point 
def AllChTCoefficients():
    tabcoeffscopy = load('TabCoeffs.sobj')
    #tabvaluescopy = load('TabValues.sobj')
    #tabvaluescopy[tabcoeffscopy.keys()[0]], tabvaluescopy[tabcoeffscopy.keys()[1]],tabvaluescopy[tabcoeffscopy.keys()[2]] = 1,0,1
    #tabvaluescopy[tabcoeffscopy.keys()[3]], tabvaluescopy[tabcoeffscopy.keys()[4]],tabvaluescopy[tabcoeffscopy.keys()[5]] = 1,0,-1
    #tabvaluescopy[tabcoeffscopy.keys()[6]],tabvaluescopy[tabcoeffscopy.keys()[7]] = -1,0
    #save(tabvaluescopy,'TabValues')
    entry = 0
    for tab in tabcoeffscopy.keys()[entry:]:
        output = OneChTCoefficient(tab,tabcoeffscopy[tab])
    return True



    
def OneChTCoefficient(tab,ulist):
    tabvaluescopy = load('TabValues.sobj')
    print "computing the standard monomial coefficient of ", tab, "so far built ", len(tabvaluescopy.keys()), "coefficients, this guy has", len(ulist), "KL values to compute"
    if tab in tabvaluescopy:
        print "already compute the coefficient of this tableau, it was ", tabvaluescopy[tab]
        return True    
    if max([u.length() for u in ulist])>30:        
        print "skipped because there is a big permutation"
        return True
    if len(ulist)>32:
        print "skipped because there are too many permutations"
        return True
    ctr = 1
    for u in ulist:
        if ctr:    
            W = u.parent()
            s = W.simple_reflections()
            print W
            break
    q = LaurentPolynomialRing(QQ,'q').gens()[0]
    KL = KazhdanLusztigPolynomial(W,q)
    w0=W.long_element()
    #w = LongestPerm(A,B)
    print "using hard-coded w"
    w = s[2]*s[4]*s[6]
    print "longest perm in the double coset is ", w
    tabcoeff = 0
    for u in ulist:
        print u, "starting this KL computation"    
        tabcoeff+= (-1)**((u*w).length())*(KL.P(u*w0, w*w0)(1))
        print "ending this KL computation", tabcoeff
    print "finished  the computation "
    tabvaluescopy[tab] = tabcoeff
    save(tabvaluescopy,'TabValues')            
    return True    

    

        
     
     


     


 
 
# test = ChTSupport([1,2,3,4,4,5,5,6],[3,4,4,5,5,6,7,8],3,9)

            
#def SegmentToPlucker(S):
#    output = []
#    for s in S:
#        Plucker = [x for x in range(1-s[0],1-s[0]+4)]
#        #print s,Plucker,3-s[1]
#        if Plucker.count(3-s[1]):
#            Plucker.remove(3-s[1])        
#            output.append(Plucker)
#        else:
#            return False
#    return output    

#    Indices = [[1,2,3,4],[2,3,4,5],[2,3,4,5],[3,4,5,6]]
#    for i in Indices:
#        if     

    
