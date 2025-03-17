
F4Vec := FullRowSpace(Rationals, 4); # Euclidean space (with standard inner product) containing F_4

# Return list of positive short roots
_F4ShortPosRoots := function()
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
_F4LongPosRoots := function()
	local list, i, e, a, b, c, d;
	list := [];
	for i in [1..4] do
		for e in [1, -1] do
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

F4ShortPosRoots := _F4ShortPosRoots();
F4ShortRoots := Concatenation(F4ShortPosRoots, -F4ShortPosRoots);
F4LongPosRoots := _F4LongPosRoots();
F4LongRoots := Concatenation(F4LongPosRoots, -F4LongPosRoots);
F4PosRoots := Concatenation(F4ShortPosRoots, F4LongPosRoots);
F4Roots := Concatenation(F4PosRoots, -F4PosRoots);

F4CartanInt := function(a, b)
	return 2 * (a*b) / (b*b);
end;

# Returns \sigma_a(b), the reflection along a applied to b
F4Refl := function(a, b)
	return b - F4CartanInt(a,b)*a;
end;