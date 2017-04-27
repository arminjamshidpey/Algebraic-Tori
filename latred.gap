# Codes related to Rationality of Algebraic Tori.
# This file contains all codes written by myself.

Sub_Matrix:= function(G,L,M)
#Inputs: G as a finite group, L list with 2 entries showing the interval of desired rows, M list with 2 
# entries showing the interval of desired columns. The output is a list containing extracted submatrices
# from generators of group G. 
local g,H;
H:= [];
	for g in GeneratorsOfGroup(G) do 
		Append(H,[g{[L[1]..L[2]]}{[M[1]..M[2]]}]);
	od;
return(H);
end;


GDual:= function(G)
# this function returns the dual G-lattice, by transposing the generators of G.

	local i,L,n,T,Gp;

	T:= GeneratorsOfGroup(G);

	n:= Size(T);

	L:=[];
	for i in [1..n] do 
		L[i]:= TransposedMat(T[i]);
	od;

	Gp:= GroupByGenerators(L);
	return(Gp);
end;


Rank1PermQuot:= function(G)

local   Denom,		# List of all denominators of entries of a vector.
	SDenom,		# Size of Denom.
	gens,		# A generating list for the rank m-1 subgroup (sublattice
			# of the dual lattice).
	H,		# The Corresponding group of the dual lattice.
	HH,		# A list of Generators of H.
	I,		# Identity matrix of size equal to rank of G
	K,		# An appropriate conjugate of the dual group in which,
			# the invariant sublattice of rank m-1 is readable.
	L,		# The record containing the vectors which extend
			# the sign vector to a basis fo lattice.
	LCM,		# The least common multiple of Denom.
	m,		# The rank of group
	W,		# A list of vectors which is formed by bases of eigenspaces.
	R,		# A mutable copy of extended basis.
	r,		# A mutable copy of the basis for the invariant space.
	S,		# GAP ID of the rank n-1 invariant for the original lattice.
	G1,		# The group asocciated to an invariant subspace of rank m-1 in the original lattice.
	Res;		# Record containing all the information of the reduction process.
	H:= GDual(G);
	HH:= GeneratorsOfGroup(H);
	m:= Size(HH[1]);
	I:= HH[1]^0;
	W:= BaseFixedSpace(HH);
	
	if Size(W)<>0 then
		if ForAll(W[1], IsInt) = false then
			Denom := List(W[1], w-> DenominatorRat(w));
			LCM:= Denom[1];
			SDenom:= Size(Denom);
			for i in [2..SDenom] do
				LCM:= LcmInt(LCM,Denom[i]);
			od;
			W[1]:= LCM*W[1];
		else
			W[1]:= W[1];
		fi;
		L:= ComplementIntMat(I,[W[1]]);
		R:= ShallowCopy(L.complement);
		r:= ShallowCopy(L.sub);
		Append(R,r);
		if IsInt(Determinant(R)) = true and AbsInt(Determinant(R))=1 then
			K:= ConjugateGroup(H,R^(-1));
			gens:= Sub_Matrix(K,[1,m-1],[1,m-1]);
			G1:= GDual(GroupByGenerators(gens));
			S:= CrystCatZClass(G1);
			Res:= rec(Structure:= StructureDescription(G), DualGens:= HH, Trans:= R^(-1), 		 				NewG:=GeneratorsOfGroup(GDual(K)),SubLatGens:= GeneratorsOfGroup(G1), ZClassSubLat:= S);	
			return(S);
		else
			return(fail);
		fi;
	else
		#Print("No Permutation lattice of Rank 1\n");
		return(fail);
		
	fi;
end;

###### For a given lattice (represented by finite number of unimodular matrices)
# The function calculates intersections of Eigenspaces for eigenvalues one and 
# negative one. In Case that there is a nonzero intersection, it returns the basis.
# Input:  a finite subgroup of GL(n,Z).
# Output: The conjugation element for the dual lattice which is a matrix in GL(n,Z).
#	  An invariant sublattice of the corresponding lattice to G, of rank 4 where
#	  the quotient of the original lattice and the output is a sign permutation. 

Rank1SgnPermQuot:= function(G)

local   
	BEigSP,		# Duplicate free list of bases of intersection of eigenspaces.
	EigSp,		# List of all eigenspaces of all generators of G.
	EigSP,		# List of Cartesian product of EigSp.
	Denom,		# List of all denominators of entries of a vector.
	gens,		# A generating list for the rank 4 subgroup (invariant sublattice
			# of the dual lattice).
	H,		# The Corresponding group of the dual lattice.
	HH,		# A list of Generators of H.
	I,		# Identity Matrix of rank 5.
	InterEigSP,	# A list of Intersections of eigenspaces.		
	K,		# An appropriate conjugate of the dual group in which,
			# the invariant sublattice of rank 4 is easily readable.
	l,		# rank of lattice
	L,		# The record containing the vectors which extend
			# the sign vector to a basis fo lattice.
	LCM,		# The least common multiple of Denom.
	W,		# A list of vectors which is formed by bases of eigenspaces.
	R,		# A mutable copy of extended basis.
	Rec,
	r,		# A mutable copy of the basis for the sign invariant space.
	S,		# GAP ID of the rank n-1 invariant for the original lattice.
	Sgen,		# The size of a generating set of H.	
	G1;		# An invariant subspace of rank 4 in the original lattice.

	H:= GDual(G);
	HH:= GeneratorsOfGroup(H);
	I:= HH[1]^0;
	l:= Size(I);
	Sgen:= Size(HH);
	EigSp:= List([1..Sgen],x->[]);
	for i in [1..Sgen] do
		Append(EigSp[i],Eigenspaces(Rationals,HH[i]));
	od;
	EigSP:= Cartesian(EigSp);
	InterEigSP:= [];
	for a in EigSP do 
		n:= Size(a);
		S:= a[1];
		for i in [2..n] do
			S:= Intersection(S,a[i]);
		od;
		Append(InterEigSP,[S]);
	od;
	BEigSP:= Set(List(InterEigSP,t->GeneratorsOfVectorSpace(t)));
	Remove(BEigSP,Position(BEigSP,[])); 
	if BEigSP <> [] then
		W:= ShallowCopy(BEigSP[1]);

		if Size(W)<>[] then
			if ForAll(W[1], IsInt) = false then
				Denom := List(W[1], w-> DenominatorRat(w));
				LCM:= Denom[1];
				for i in [2..Size(Denom)] do
					LCM:= LcmInt(LCM,Denom[i]);
				od;
				W[1]:= LCM*W[1];
			else
				W[1]:= W[1];
			fi;
			L:= ComplementIntMat(I,W);
			R:= ShallowCopy(L.complement);
			r:= ShallowCopy(L.sub);
			Append(R,r);
				
				K:= ConjugateGroup(H,R^(-1));
				gens:= Sub_Matrix(K,[1,l-1],[1,l-1]);
				G1:= GDual(GroupByGenerators(gens));
				S:= CrystCatZClass(G1);
				Print(R^(-1),"\n");
				Rec:= rec(DualGens:= HH, Trans:= R^(-1), NewG:= GeneratorsOfGroup(GDual(K)),
                                         SubLatGens:= GeneratorsOfGroup(G1), ZClassSubLat:= S);				
					return(S);
		else
			Print("No sign permutation lattice of rank 1\n");
		
		fi;
	else
		Print("No sign permutation lattice of rank 1\n");
	fi;
end;


