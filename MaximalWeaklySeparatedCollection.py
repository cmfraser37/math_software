'''
Weakly Separated Collection Class following Oh-Postnikov-Speyer
extend_to_maximal takes a weakly separated collection and greedily expands it to a maximal one
the class also knows the quiver of the maximal weakly separated collection and knows how to plot its plabic tiling
'''




class WeaklySeparatedCollection(SageObject):
    def __init__(self,CC,n):
        self._collection = CC
        self._size = len(CC)
        self._k = len(CC[0])
        self._n = n
        CCdict = {}
        ctr = 0
        for S in CC:
            CCdict[tuple(S)] = ctr
            ctr+= 1
        self._dictionary = CCdict

    def collection_to_dictionary(self):		
        CC = self._collection
        CCdict = {}
        ctr = 0
        for S in CC:
            CCdict[tuple(S)] = ctr
            ctr+= 1
        self._dictionary = CCdict

    def is_maximal(self):
        return (self._size == (self._k)*(self._n-self._k)+1)
	
		
    def extend_to_maximal(self):
        n = self._n
        k = self._k
        CC = self._collection
        SS = sorted([list(x) for x in Subsets(range(1,n+1),k)])
        SSnew = copy(SS)
        for X in SS:
            for Y in CC:
                if X == Y or (not weakly_separated(X,Y)):  
                    SSnew.remove(X)
                    break
        SS = copy(SSnew)
        while len(SS):
            S = SS[0]
            self._collection.append(S)
            SSnew = copy(SS)
            for X in SS:
                if X == S or (not weakly_separated(X,S)):  
                    SSnew.remove(X)
            SS = copy(SSnew)
        self.frozens_at_end()
        self.collection_to_dictionary()	
        self._size = len(self._collection)
	
    def frozens_at_end(self):
        k = self._k
        n = self._n
        frozen_list = [sorted([x%n+1 for x in range(i,i+k)]) for i in range(n)]
        CC = copy(self._collection)
        for x in frozen_list:
            CC.append(CC.pop(CC.index(x)))
        self._collection = copy(CC)
        self.collection_to_dictionary()



    def white_black_cliques(self):
        self.frozens_at_end()
        n = self._n
        CC = self._collection
        WW = []
        for C in CC:
            for i in C:
                K = sorted(listminus(C,i))
                if K not in WW:
                    WW.append(K)
        BB = []
        for C in CC:
            for i in listcomplement(range(1,n+1), C):
                K = sorted(C+[i])
                if K not in BB:
                    BB.append(K)
        return WW, BB	


    def quiver(self):
        k = self._k
        n = self._n		
        NN = self._size
        CC = self._collection
        CCdict = self._dictionary		
        WW, BB = self.white_black_cliques()

        edges = []
        for W in WW:
            X = [i for i in range(1,n+1) if sorted(W+[i]) in CC]			
            if len(X) >= 3:
                edges += [[sorted(W+[X[len(X)-1]]), sorted(W+[X[0]])]]
                edges += [[sorted(W+[X[j]]),sorted(W+[X[j+1]])] for j in range(len(X)-1)]
        for B in BB:
            Y = sorted([j for j in B if sorted(listminus(B,j)) in CC], reverse=True)
            if len(Y) >= 3:
                edges += [[sorted(listminus(B, Y[len(Y)-1])), sorted(listminus(B, Y[0]))]]
                edges += [ [sorted(listminus(B, Y[j])), sorted(listminus(B, Y[j+1]))] for j in range(len(Y)-1)] 
        edgesNew = []
        for e in edges:
            if e not in edgesNew:
                edgesNew.append(e)
        edges = edgesNew

        B = [[0 for i in range(NN)] for j in range(NN)]
        for e in edges:
            i,j = CCdict[tuple(e[0])], CCdict[tuple(e[1])]
            B[i][j] += 1
            B[j][i] += -1
        return B	
        
        


    def plabic_tiling(self, regions_color = 'gray', nodes_color = 'red'):
        r = 1
        k = self._k 
        NN = self._size
        n = self._n
        CC = self._collection
        CCdict = self._dictionary
        WW, BB = self.white_black_cliques()
        frozen_list = [sorted([x%n+1 for x in range(i,i+k)]) for i in range(n)]

        regions_plot = plot([], axes = False)
        nodes_plot = plot([], axes = False)
        vertex_list = [(r*cos(2*pi*i/n),r*sin(2*pi*i/n)) for i in range(n)]
        CC_xycoords = [(sum([vertex_list[i-1][0] for i in x]),sum([vertex_list[i-1][1] for i in x]))  for x in CC]
        CC_strings = ['$' + ''.join([str(y) for y in x])  + '$' for x in CC]

        for i in range(n):
            regions_plot += line([CC_xycoords[CCdict[tuple(frozen_list[i-1])]],CC_xycoords[CCdict[tuple(frozen_list[i])]]], color = regions_color)

        for B in BB:
            Y = sorted([j for j in B if sorted(listminus(B,j)) in CC], reverse=True)
            if len(Y) >= 3:
                regions_plot += polygon([CC_xycoords[CCdict[tuple(sorted(listminus(B, j)))]] for j in Y], color = regions_color, fill = True)			

        for i in range(NN):
            nodes_plot += point((CC_xycoords[i]), pointsize = 800, color = nodes_color, marker = CC_strings[i])
            nodes_plot[i].set_zorder(2)
		
        out_plot = regions_plot + nodes_plot
        return out_plot
