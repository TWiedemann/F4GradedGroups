
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

A2Roots := [[1,-1,0], [1,0,-1], [0,1,-1], [0,-1,1], [-1,0,1], [-1,1,0]];

F4CartanInt := function(a, b)
	return 2 * (a*b) / (b*b);
end;

# Returns \sigma_a(b), the reflection along a applied to b
F4Refl := function(a, b)
	return b - F4CartanInt(b, a)*a;
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
		return [2, -1];
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