### The root system F4 and the rea

# ----- Basic setup: Global variables -----

F4Vec := FullRowSpace(Rationals, 4); # Euclidean space (with standard inner product) containing F4

# Return list of positive short roots in F4 in the dual of the "standard Bourbaki description"
_F4ShortRoots := function()
	local list, i, j, ei, ej, a;
	list := [];
	for i in [1..4] do
		for j in [i+1..4] do
			for ei in [1, -1] do
				for ej in [1, -1] do
					a := [0, 0, 0, 0];
					a[i] := ei;
					a[j] := ej;
					Add(list, a);
				od;
			od;
		od;
	od;
	return list;
end;

# Return list of positive long roots in F4
_F4LongRoots := function()
	local list, i, e, a, b, c, d;
	list := [];
	for i in [1..4] do
		for e in [2, -2] do
			a := [0,0,0,0];
			a[i] := e;
			Add(list, a);
		od;
	od;
	for a in [1,-1] do
		for b in [1, -1] do
			for c in [1, -1] do
				for d in [1, -1] do
					Add(list, [a, b, c, d]);
				od;
			od;
		od;
	od;
	return list;
end;

# Sets of roots in F4
F4ShortRoots := _F4ShortRoots();
F4LongRoots := _F4LongRoots();
F4Roots := Concatenation(F4ShortRoots, F4LongRoots);
F4RootsZero := Concatenation(F4Roots, [[0,0,0,0]]);
F4SimpleRoots := [[1,1,-1,-1], [-2, 0, 0, 0], [1, -1, 0, 0], [0, 1, 1, 0]]; # Dynkin diagram: 1-2>3-4
F4SimpleRootsBas := Basis(F4Vec, F4SimpleRoots); # Simple roots as a vector space basis in GAP

# Sets of roots in G2
G2ShortRoots := [[-1,-1], [-1,0], [0,-1], [0,1], [1,0], [1,1]];
G2LongRoots := [[-2,-1], [-1,-2], [-1,1], [1,-1], [1,2], [2,1]];
G2Roots := Concatenation(G2ShortRoots, G2LongRoots);

# Set of roots in A2
A2Roots := [[1,-1,0], [1,0,-1], [0,1,-1], [0,-1,1], [-1,0,1], [-1,1,0]];

# root: Root in F4
# Returns: List a of coefficients w.r.t. F4SimpleRoots. Thus root = a*F4SimpleRoots.
F4RootBasisCoeffs := function(root)
	return Coefficients(F4SimpleRootsBas, root);
end;

F4RootFromBasisCoeffs := function(coeffs)
	return coeffs * F4SimpleRoots;
end;

F4PosRoots := Filtered(F4Roots, root -> Sum(F4RootBasisCoeffs(root)) > 0);
F4NegRoots := Difference(F4Roots, F4PosRoots);
F4PosShortRoots := Intersection(F4PosRoots, F4ShortRoots);
F4PosLongRoots := Intersection(F4PosRoots, F4LongRoots);
F4NegShortRoots := Intersection(F4NegRoots, F4ShortRoots);
F4NegLongRoots := Intersection(F4NegRoots, F4LongRoots);

F4ParityList := fail; # Not yet implemented

# ----- Functions on root systems -----

# a, b: Roots in F4.
# Returns: The Cartan integer of (a, b).
# Since our representation of F4 is the dual of the Bourbaki representation,
# the bilinear form on F4 is simply the usual inner product, given by *
F4CartanInt := function(a, b)
	return 2 * (a*b) / (b*b);
end;

# a, b: Roots in G2.
# Returns: a*b where * represents the bilinear form on G2
G2BilinearForm := function(a, b)
	local mat;
	# mat[i][j] = e_i*e_j where e_1 = [1, 0], e_2 =  [0, 1]
	mat := [ [2, -1], [-1, 2] ];
	return a*mat*b;
end;

# a, b: Roots in G2.
# Returns: The Cartan integer of (a, b).
G2CartanInt := function(a,b)
	return 2 * G2BilinearForm(a,b) / G2BilinearForm(b,b);
end;

# argRoot, reflRoot: Roots in F4
# Returns: argRoot^{\sigma_reflRoot}, the reflection along reflRoot applied to argRoot
F4Refl := function(argRoot, reflRoot)
	return argRoot - F4CartanInt(argRoot, reflRoot)*reflRoot;
end;

# argRoot: Root in F4
# reflRootList: List [a_1, ..., a_k] of roots in F4
# Returns: argRoot^{\sigma(a_1) ... \sigma(a_k)}
F4ReflProd := function(argRoot, reflRootList)
	local result, reflRoot;
	result := argRoot;
	for reflRoot in reflRootList do
		result := F4Refl(result, reflRoot);
	od;
	return result;
end;

# rootList1, rootList2: Lists [a_1,...,a_k], [b_1,...,b_m] of roots in F4
# Returns: True if \sigma(a_1...a_k) = \sigma(b_1...b_m), otherwise false
F4ReflProdEqual := function(rootList1, rootList2)
	local root;
	for root in F4Roots do
		if F4ReflProd(root, rootList1) <> F4ReflProd(root, rootList2) then
			return false;
		fi;
	od;
	return true;
end;

# root: Element of F4Roots or [0,0,0,0]
# Returns: The corresponding root in G2
F4RootG2Coord := function(root)
	return [root[1], Sum(root)/2];
end;
