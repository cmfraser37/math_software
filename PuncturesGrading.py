def ComputeWClusters(tol,M):
    if M == 4:
        R = LaurentPolynomialRing(ZZ,4,['w1','w2','w3','w4'])
        w1,w2,w3,w4 = R.gens()
        winit = [w1,w1*w3,w1*w2*w3,w1,w1*w2,w1*w2*w3]
        possiblemonomials = [1,w1,w2,w3,w1*w2,w1*w3,w2*w3,w1*w2*w3,1/(w1*w2*w3),1/(w1*w3),1/(w2*w3),1/(w1*w2),1/w1,1/w2,1/w3]
        replacementmonomials = [1,w1,w2,w3,w1*w2,w1*w3,w2*w3,w1*w2*w3,w4,w2*w4,w1*w4,w3*w4,w2*w3*w4,w1*w3*w4,w1*w2*w4]  
    elif M ==3:
        R = LaurentPolynomialRing(ZZ,3,['w1','w2','w3'])
        w1,w2,w3 = R.gens()
        winit = [w1,w1,w1,w1*w2,w1*w2,w1*w2]
        possiblemonomials = [1,w1,w2,w1*w2,1/(w1*w2),1/w1,1/w2]
        replacementmonomials = [1,w1,w2,w1*w2,w3,w2*w3,w1*w3]        
    InitMatrix = matrix([[0,-1,1,1,-1,0],[1,0,-1,-1,0,1],[-1,1,0,0,1,-1],[-1,1,0,0,1,-1],[1,0,-1,-1,0,1],[0,-1,1,1,-1,0]])
    Qinit = ClusterQuiver(InitMatrix)
    winitms = [winit.count(x) for x in possiblemonomials]
    # build 4 quiver isomorphism representatives
    Qcop = ClusterQuiver(InitMatrix)
    Q0 = Qcop.digraph()
    Qcop.mutate(4)
    Q1 = copy(Qcop).digraph()
    Qcop.mutate(3)
    Q2 = copy(Qcop).digraph()
    Qcop.mutate(2)
    Q3 = copy(Qcop).digraph()
    Qtypes = [Q0,Q1,Q2,Q3]
    G = Graph()     #graph whose vertices are w-clusters with their quiver type
    SPG = Graph()   # graph whose vertices are set-partitions with adjacencies given by mutation
    OSP = OrderedSetPartitions(M).list()
    N = len(OSP)
    SPtoWcluster = [[OSP[osp]] for osp in range(N)] # for each OSP, the list of quivers and w-clusters attaining it      
    wtemp = copy(winit)
    PairsToVisit = [(wtemp,0,[])]
    G.add_vertex(("".join([str(x) for x in wtemp]),0))
    SPG.add_vertex(CoarsestSetPartition(R,[replacementmonomials[possiblemonomials.index(x)] for x in wtemp]))        
    PairsVisited = [(copy(winitms),0)]
    ctr = 0    
    #tol should be set at 13
    while ctr < tol:
        nextPairsToVisit = []
        for Pair in PairsToVisit:
            Qcop = ClusterQuiver(InitMatrix)
            Qcop.mutate(Pair[2])
            currentstate = (copy([Pair[0].count(x) for x in possiblemonomials]),Pair[1])
            currentvtx = ("".join([str(x) for x in Pair[0]]),Pair[1])
            currentSPvtx = CoarsestSetPartition(R,[replacementmonomials[possiblemonomials.index(x)] for x in Pair[0]])
            currentQstate = [i for i in range(4) if Qcop.digraph().is_isomorphic(Qtypes[i])][0]
            SPtoWcluster[OSP.index(currentSPvtx)].append((currentQstate,TrimWCluster(R,[replacementmonomials[possiblemonomials.index(x)] for x in Pair[0]])))
            for symbol in range(6):
                wtemp = copy(Pair[0])            
                neww = 1/wtemp[symbol]
                posnbrs = [[Qcop.b_matrix()[symbol][nbr],wtemp[nbr]] for nbr in range(6) if Qcop.b_matrix()[symbol][nbr] >0]
                Qcop.mutate(symbol)
                Qstate = [i for i in range(4) if Qcop.digraph().is_isomorphic(Qtypes[i])][0]
                Qcop.mutate(symbol)
                for posnbr in posnbrs:
                    neww *= posnbr[1]**posnbr[0]
                wtemp[symbol] = neww
                newstate = ([wtemp.count(x) for x in possiblemonomials],Qstate)
                newvtx = ("".join([str(x) for x in wtemp]),Qstate)      
                partttition = CoarsestSetPartition(R,[replacementmonomials[possiblemonomials.index(x)] for x in wtemp])
                if PairsVisited.count(newstate) == 0:
                    #print "Quiver: ", Qstate, "cluster: ", TrimWCluster(R,[replacementmonomials[possiblemonomials.index(x)] for x in wtemp]), "Partition: ", CoarsestSetPartition(R,[replacementmonomials[possiblemonomials.index(x)] for x in wtemp])
                    SPG.add_vertex(partttition)
                    nextPairsToVisit.append((wtemp,Qstate,Pair[2]+[symbol]))
                    PairsVisited.append(newstate)
                    G.add_vertex(newvtx)
                G.add_edge([newvtx,currentvtx])
                G.add_edge([currentvtx,newvtx])                
                SPG.add_edge(partttition,currentSPvtx)   
                SPG.add_edge(currentSPvtx,partttition)                       
                    
        PairsToVisit = copy(nextPairsToVisit)
        if len(PairsToVisit) ==0:
            print "it worked"
            assert SPG == SetPartitionAdjacencyGraph(M)
            return G,SPG,SPtoWcluster
        ctr += 1
    return G,SPG, SPtoWcluster

 
 



    
def TrimWCluster(R,wcluster):
    if len(R.gens()) == 4:
        w1,w2,w3,w4 = R.gens()
        possibleterms = [1,w1,w2,w3,w4,w1*w2,w1*w3,w1*w4,w2*w3,w2*w4,w3*w4,w1*w2*w3,w1*w2*w4,w1*w3*w4,w2*w3*w4]
        output = []
        for x in possibleterms:
            if wcluster.count(x):
                output.append(x**wcluster.count(x))
    elif len(R.gens()) == 3:
        w1,w2,w3 = R.gens()
        possibleterms = [1,w1,w2,w3,w1*w2,w1*w3,w2*w3]
        output = []
        for x in possibleterms:
            if wcluster.count(x):
                output.append(x**wcluster.count(x))   
    return output    
    

def CoarsestSetPartition(R,wcluster):
    if len(R.gens()) == 3:
        wclusterset = list(set(wcluster))
        w1,w2,w3 = R.gens()
        ws = [0,w1,w2,w3]
        wclusterms = [wclusterset.count(x) for x in [1,w1,w2,w3,w1*w2,w1*w3,w2*w3]]
        if wclusterset.count(w1*w2)+wclusterset.count(w1*w3)+wclusterset.count(w2*w3) == 3:
            return OrderedSetPartition([[1,2,3]])                
        Firstblock = [x for x in [1,2,3] if wclusterms[x]>0]
        Secondblock = []
        Thirdblock = []
        for i in [1,2,3]:        
            for j in range(i+1,4):
                if wclusterset.count(ws[i]*ws[j]):
                    if Firstblock.count(i)+Firstblock.count(j) ==2:
                        continue
                    elif Firstblock.count(i):
                        Secondblock.append(j)
                    elif Firstblock.count(j):
                        Secondblock.append(i)
                                                
        output = []
        Thirdblock = [x for x in [1,2,3] if x not in Firstblock and x not in Secondblock]
        for F in [Firstblock,Secondblock,Thirdblock]:
            if len(F) >0:
                output.append(F)
        return OrderedSetPartition(output)            

    #otherwise, do SL4 case. 
    wclusterset = list(set(wcluster))
    w1,w2,w3,w4 = R.gens()
    ws = [0,w1,w2,w3,w4]
    wclusterms = [wclusterset.count(x) for x in [1,w1,w2,w3,w4,w1*w2,w1*w3,w1*w4,w2*w3,w2*w4,w3*w4,w1*w2*w3,w1*w2*w4,w1*w3*w4,w2*w3*w4]]
    if wclusterset.count(w1*w2*w3)+wclusterset.count(w1*w2*w4)+wclusterset.count(w1*w3*w4)+wclusterset.count(w2*w3*w4) == 4:
        return OrderedSetPartition([[1,2,3,4]])        
    elif wclusterset.count(ws[1]*ws[2])+ wcluster.count(ws[1]*ws[3])+ wcluster.count(ws[2]*ws[3])==3:
        #print 'A'
        #print "dual thing happened in first block"        
        return OrderedSetPartition([[1,2,3],[4]])
    elif wclusterset.count(ws[1]*ws[2])+ wcluster.count(ws[1]*ws[4])+ wcluster.count(ws[2]*ws[4])==3:
        #print 'B'
        #print "dual thing happened  in first block"        
        return OrderedSetPartition([[1,2,4],[3]])
    elif wclusterset.count(ws[1]*ws[3])+ wcluster.count(ws[1]*ws[4])+ wcluster.count(ws[3]*ws[4])==3:
        #print 'C'
        #print "dual thing happened  in first block"        
        return OrderedSetPartition([[1,3,4],[2]])
    elif wclusterset.count(ws[2]*ws[3])+ wcluster.count(ws[2]*ws[4])+ wcluster.count(ws[3]*ws[4])==3:
        #print 'D'
        #print "dual thing happened in first block"        
        return OrderedSetPartition([[2,3,4],[1]])
    for i in [1,2,3,4]:
        if sum([wclusterset.count(ws[i]*ws[j]) for j in [1,2,3,4]]) ==3:
            #print 'E'
            return OrderedSetPartition([[i],[x for x in [1,2,3,4] if x != i]])
        elif sum([wclusterset.count(ws[i]*ws[j]*ws[k]) for [j,k] in [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]]) ==3:
            #print 'F',i
            #print "dual thing happened  in second block"
            return OrderedSetPartition([[i],[x for x in [1,2,3,4] if x != i]])                   
        
    Firstblock = [x for x in [1,2,3,4] if wclusterms[x]>0]
    Secondblock = []
    Thirdblock = []

    for i in [1,2,3,4]:        
        for j in range(i,5):
            if wclusterset.count(ws[i]*ws[j]):
                if Firstblock.count(i)+Firstblock.count(j) ==2:
                    #print 'G'
                    continue
                elif Firstblock.count(i):
                    #print 'H'
                    Secondblock.append(j)
                elif Firstblock.count(j):
                    #print 'I'
                    Secondblock.append(i)
    #print Firstblock,Secondblock
    for i in [1,2,3,4]:
        for j in range(i,5):
            for k in range(j,5):
                if wclusterset.count(ws[i]*ws[j]*ws[k]):
                    if Firstblock.count(i)+Firstblock.count(j)+Firstblock.count(k)+Secondblock.count(i)+Secondblock.count(j)+Secondblock.count(k) ==3:
                        #print 'J'
                        continue
                    elif Firstblock.count(i)+Firstblock.count(j)+Secondblock.count(i)+Secondblock.count(j)==2:
                        #print 'K'
                        Thirdblock.append(k)
                    elif Firstblock.count(i)+Firstblock.count(k)+Secondblock.count(i)+Secondblock.count(k)==2:
                        #print 'L'
                        Thirdblock.append(j)
                    elif Firstblock.count(j)+Firstblock.count(k)+Secondblock.count(j)+Secondblock.count(k)==2:
                        Thirdblock.append(i)
                        
                        
    output = []
    Fourthblock = [x for x in [1,2,3,4] if x not in Firstblock and x not in Secondblock and x not in Thirdblock]
    for F in [Firstblock,Secondblock,Thirdblock,Fourthblock]:
        if len(F) >0:
            output.append(F)
    return OrderedSetPartition(output)            
                    
def SetPartitionAdjacencyGraph(N):
    G = Graph()
    for OSP in OrderedSetPartitions(N):
        G.add_vertex(OSP)
    n = len(G.vertices())
    for i in range(n):
        S = G.vertices()[i]
        listS = [set(list(x)) for x in S]
        ls = len(listS)
        for j in range(ls-1):
            if len(listS[j]) == 1:
                newthing = copy(listS[:j] + listS[j+1:])
                #print "before merge:",listS,newthing
                newthing[j] = newthing[j].union(listS[j])
                #print "after merge:",listS,newthing
                G.add_edge(S,OrderedSetPartition(newthing))
                G.add_edge(OrderedSetPartition(newthing),S)
        for j in range(1,ls):
            if len(listS[j]) == 1:
                newthing = copy(listS[:j] + listS[j+1:])
                #print "before merge:",listS,newthing
                newthing[j-1] = newthing[j-1].union(listS[j])
                #print "after merge:",newthing
                G.add_edge(S,OrderedSetPartition(newthing))
                G.add_edge(OrderedSetPartition(newthing),S)

                
        for j in range(i+1,n):
            T = G.vertices()[j]
            listT = [set(list(x)) for x in T]
            lt = len(listT)           
            if ls == lt:
                discrepancy = [len(listS[k].symmetric_difference(listT[k])) for k in range(ls) if len(listS[k].symmetric_difference(listT[k]))]
                discrepancyks = [k for k in range(ls) if len(listS[k].symmetric_difference(listT[k]))]
                if len(discrepancyks) == 2:
                    if (discrepancyks[1]-discrepancyks[0] == 1) and (discrepancy[0] == 1) and (discrepancy[1] ==1):
                        G.add_edge(S,T)
                        G.add_edge(T,S)
                        
    return G            
            
    
        
        
                    
    
    
    