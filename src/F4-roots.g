
F4Vec := FullRowSpace(Rationals, 4); # Euclidean space (with standard inner product) containing F_4

# Return list of positive short roots
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

# Return list of positive long roots
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

F4ShortRoots := _F4ShortRoots();
F4LongRoots := _F4LongRoots();
F4Roots := Concatenation(F4ShortRoots, F4LongRoots);
F4RootsZero := Concatenation(F4Roots, [[0,0,0,0]]);
F4SimpleRoots := [[1,1,-1,-1], [-2, 0, 0, 0], [1, -1, 0, 0], [0, 1, 1, 0]]; # Dynkin diagram: 1-2>3-4
F4SimpleRootsBas := Basis(F4Vec, F4SimpleRoots); # Simple roots as a vector space basis in GAP

# root: Root in F4
# Output: List a of coefficients w.r.t. F4SimpleRoots. Thus root = a*F4SimpleRoots.
F4RootBasisCoeffs := function(root)
	return Coefficients(F4SimpleRootsBas, root);
end;

F4RootFromBasisCoeffs := function(coeffs)
	return coeffs * F4SimpleRoots;
end;

F4SimpleRootFromIndex := function(i)
	if i > 0 then
		return F4SimpleRoots[i];
	else
		return F4SimpleRoots[-i];
	fi;
end;

F4PosRoots := Filtered(F4Roots, root -> Sum(F4RootBasisCoeffs(root)) > 0);
F4NegRoots := Difference(F4Roots, F4PosRoots);
F4PosShortRoots := Intersection(F4PosRoots, F4ShortRoots);
F4PosLongRoots := Intersection(F4PosRoots, F4LongRoots);
F4NegShortRoots := Intersection(F4NegRoots, F4ShortRoots);
F4NegLongRoots := Intersection(F4NegRoots, F4LongRoots);

A2Roots := [[1,-1,0], [1,0,-1], [0,1,-1], [0,-1,1], [-1,0,1], [-1,1,0]];

F4CartanInt := function(a, b)
	return 2 * (a*b) / (b*b);
end;

# Returns argRoot^{\sigma_reflRoot}, the reflection along reflRoot applied to argRoot
F4Refl := function(argRoot, reflRoot)
	return argRoot - F4CartanInt(argRoot, reflRoot)*reflRoot;
end;

F4ReflProd := function(argRoot, reflRootList)
	local result, reflRoot;
	result := argRoot;
	for reflRoot in reflRootList do
		result := F4Refl(result, reflRoot);
	od;
	return result;
end;

F4ReflProdEqual := function(rootList1, rootList2)
	local root;
	for root in F4Roots do
		if F4ReflProd(root, rootList1) <> F4ReflProd(root, rootList2) then
			return false;
		fi;
	od;
	return true;
end;

# a: A root in F4.
# Output: List of all roots in F4 which are orthogonal to a.
F4OrthoRoots := function(a)
	local result, b;
	result := [];
	for b in F4Roots do
		if a*b = 0 then
			Add(result, b);
		fi;
	od;
	return result;
end;

F4PosOrthoRoots := function(a)
	return Intersection(F4PosRoots, F4OrthoRoots(a));
end;

# root: Element of F4Roots or [0,0,0,0]
# Output: The corresponding root in G2
F4RootG2Coord := function(root)
	local sum;
	if not root in F4RootsZero then
		Error("Not a root in F4");
		return fail;
	fi;
	# L_2
	if root = [2, 0, 0, 0] then
		return [2, 1];
	# L_{-2}
	elif root = [-2, 0, 0, 0] then
		return [-2, -1];
	# ComRing-parts of the Brown algebra
	elif root = [-1, -1, -1, -1] then
		return [-1, -2];
	elif root = [-1, 1, 1, 1] then
		return [-1, 1];
	elif root = [1, -1, -1, -1] then
		return [1, -1];
	elif root = [1, 1, 1, 1] then
		return [1, 2];
	# L_0
	elif root[1] = 0 then
		sum := Sum(root);
		if sum = 0 then
			return [0, 0];
		elif sum > 0 then
			return [0, 1];
		else
			return [0, -1];
		fi;
	# Cubic-parts of L_{-1}
	elif root[1] = -1 then
		if Sum(root) = 0 then
			return [-1, 0];
		else
			return [-1, -1];
		fi;
	# Cubic-parts of L_1
	else
		if Sum(root) = 0 then
			return [1, 0];
		else
			return [1, 1];
		fi;
	fi;
end;

# root: in F4
# Returns list of all pairs [ root1, root2 ] s.t. root1 + root2 = root and
# root1 appears in F4Roots before root2
F4SumDecomp := function(root)
	local result, i, j, root1, root2;
	result := [];
	for i in [1..Length(F4Roots)] do
		root1 := F4Roots[i];
		for j in [i+1..Length(F4Roots)] do
			root2 := F4Roots[j];
			if root1 + root2 = root then
				Add(result, [root1, root2]);
			fi;
		od;
	od;
	return result;
end;

PrintF4SumDecomp := function(root)
	local entry;
	for entry in F4SumDecomp(root) do
		Print(entry[1], " * ", entry[2], "\n");
	od;
end;

# Returns a table par such that par[i][j] is the parity of w_{F4SimpleRoots[j]} on
# U_{F4Roots[i]}
_ComputeF4ParityList := function()
	local d1Par, d2Par, d3Par, d4Par, dPar, root, d1, d2, d3, d4, par, list, j;
	d1 := F4SimpleRoots[1];
	d2 := F4SimpleRoots[2];
	d3 := F4SimpleRoots[3];
	d4 := F4SimpleRoots[4];
	d1Par := NewDictionary(F4Roots[1], true, F4Roots);
	d2Par := NewDictionary(F4Roots[1], true, F4Roots);
	d3Par := NewDictionary(F4Roots[1], true, F4Roots);
	d4Par := NewDictionary(F4Roots[1], true, F4Roots);
	# d1
	for root in F4PosRoots do
		if root in [d1, d1+d2, d1+d2+d3, d1+d2+2*d3, d1+d2+2*d3+d4, d1+d2+2*(d3+d4),
			d1+3*d2+4*d3+2*d4] then
			AddDictionary(d1Par, root, [-1, 1]);
		else
			AddDictionary(d1Par, root, [1, 1]);
		fi;
		AddDictionary(d1Par, -root, LookupDictionary(d1Par, root));
	od;
	# d2
	for root in F4PosRoots do
		if root in [d1, d2, d2+d3, d2+d3+d4, d1+d2+2*d3, d1+d2+2*d3+d4,
			d1+d2+2*(d3+d4), d1+2*d2+4*d3+2*d4] then
			AddDictionary(d2Par, root, [-1, 1]);
		else
			AddDictionary(d2Par, root, [1,1]);
		fi;
		AddDictionary(d2Par, -root, LookupDictionary(d2Par, root));
	od;
	# d3
	for root in F4PosRoots do
		if root in [d2, d3, d1+d2, d2+2*d3, d1+d2+2*d3, d2+2*d3+d4,
			d1+d2+2*d3+d4, d1+2*(d2+d3)+d4, d1+2*(d2+d3+d4), d1+2*d2+4*d3+2*d4] then
			AddDictionary(d3Par, root, [-1, 1]);
		elif root in [d2+d3, d1+d2+d3, d1+2*d2+3*d3+2*d4] then
			AddDictionary(d3Par, root, [-1, -1]);
		else
			AddDictionary(d3Par, root, [1,1]);
		fi;
		AddDictionary(d3Par, -root, LookupDictionary(d3Par, root));
	od;
	# d4
	for root in F4PosRoots do
		if root in [d3, d4, d2+d3, d1+d2+d3, d2+2*d3, d1+d2+2*d3, d1+2*(d2+d3),
			d2+2*(d3+d4), d1+d2+2*(d3+d4), d1+2*(d2+d3+d4), d1+2*d2+3*d3+2*d4] then
			AddDictionary(d4Par, root, [-1, 1]);
		elif root in [d2+2*d3+d4, d1+d2+2*d3+d4, d1+2*(d2+d3)+d4] then
			AddDictionary(d4Par, root, [-1, -1]);
		else
			AddDictionary(d4Par, root, [1,1]);
		fi;
		AddDictionary(d4Par, -root, LookupDictionary(d4Par, root));
	od;
	# Build par
	dPar := [d1Par, d2Par, d3Par, d4Par];
	par := [];
	for root in F4Roots do
		list := [];
		for j in [1..4] do
			Add(list, LookupDictionary(dPar[j], root));
		od;
		Add(par, list);
	od;
	return par;
end;

F4ParityList := _ComputeF4ParityList();