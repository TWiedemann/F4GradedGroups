## Tests
PrintLieComRel := function()
	local i, j, root1, root2, root3, a1, a2, a3, count;
	count := 0;
	for i in [1..Length(F4Roots)] do
		root1 := F4Roots[i];
		if root1 in F4ShortRoots then
			a1 := ConicAlgBasicIndet(1);
		else
			a1 := ComRingBasicIndet(1);
		fi;
		for j in [i+1..Length(F4Roots)] do
			root2 := F4Roots[j];
			if root2 in F4ShortRoots then
				a2 := ConicAlgBasicIndet(2);
			else
				a2 := ComRingBasicIndet(2);
			fi;
			root3 := root1 + root2;
			if root3 in F4ShortRoots then
				a3 := ConicAlgBasicIndet(1);
			elif root3 in F4LongRoots then
				a3 := ComRingBasicIndet(1);
			else
				continue;
			fi;
			count := count+1;
			Print(root1, " * ", root2, ": ", ApplyDistAndPeirceLaw(LieRootHomF4(root1, a1) * LieRootHomF4(root2, a2)), "\n");
			Print(root3, ": ", LieRootHomF4(root3, a3), "\n\n");
		od;
	od;
	Display(count);
end;

# Does not work because e.g. ConicAlgMatTr(a1*a1') = 2*n(a1)
TestWithoutTraces := function()
	local magEls, magEl, test1, test2;
	magEls := Concatenation(_AllConicAlgMagEls(Trace_MaxLength));
	for magEl in magEls do
		test1 := WithoutTraces(ConicAlgMagTr(magEl));
		test2 := ConicAlgMagEmb(magEl) + ConicAlgMagEmb(ConicAlgMagInv(magEl));
		if test1 <> test2 then
			return magEl;
		fi;
	od;
	return true;
end;

## Tests for abstract parametrisation strategy

# relations: A list of lists [l1, l2] where l1 and l2 are lists containing elements
# from [-4, -3, -2, -1, 1, 2, 3, 4] or elements from LieEndo
# The function calls TestRelations on the list weylRelations which is obtained from relations
# by replacing any list [g1, g2, ...] by the automorphism g1 * g2 * ...
# If gi is a positive integer, it is interpreted as w_gi. If it is a negative integer,
# it is interpreted as w_(-gi)^-1. Here wj = GrpStandardWeyl(F4SimpleRoots[j]).
# Uses indeterminates t_1, a_1.
TestWeylRelations := function(relations)
	local w, wInv, i, weylRelations;
	w := [];
	wInv := [];
	for i in [1..Length(F4SimpleRoots)] do
		w[i] := GrpStandardWeylF4(F4SimpleRoots[i]);
		wInv[i] := GrpStandardWeylInvF4(F4SimpleRoots[i]);
	od;
	weylRelations := List(relations, x -> List(x, function(list)
		local auto, i;
		auto := GrpOne;
		for i in list do
			if not IsInt(i) then
				auto := auto * i;
			elif i>0 then
				auto := auto * w[i];
			else
				auto := auto * wInv[-i];
			fi;
		od;
		return auto;
	end));
	return TestRelations(weylRelations);
end;

# Prints all relations which have to be proven by hand to verify the braid relations for
# the standard Weyl elements w.r.t. F4SimpleRoots.
# Uses indeterminates a_1, t_1
TestBraidRel := function()
	return TestWeylRelations([
		[[1, 2, 1], [2, 1, 2]], [[1, 3], [3, 1]], [[1, 4], [4, 1]],
		[[2, 3, 2, 3], [3, 2, 3, 2]], [[2, 4], [4, 2]],
		[[3, 4, 3], [4, 3, 4]]
	]);
end;

# Denote by wi the standard Weyl element for F4SimpleRoots[i]
# This function prints all relations which have to be proven by hand to verify the
# following assertions:
# wi^(wj^2) = wi^-1, wj^(wi^1) = wj^-1 for (i, j) \in {(1,2), (3,4)}
# w2^(w3^2) = w2, w3^(w2^2) = w3^-1
# Note that for i, j with |i-j| > 1, we know from the braid relations that
# wi^(wj^2) = wi.
# Uses indeterminates t_1, a_1.
TestWeylSquareOnWeyl := function()
	return TestWeylRelations([
		[[-1, -1, 2, 1, 1], [-2]], [[-2, -2, 1, 2, 2], [-1]],
		[[-3, -3, 4, 3, 3], [-4]], [[-4, -4, 3, 4, 4], [-3]],
		[[-2, -2, 3, 2, 2], [-3]], [[-3, -3, 2, 3, 3], [2]]
	]);
end;

# Denote by wi the standard Weyl element for F4SimpleRoots[i] by d2, d3 the simple
# roots of index 2 and 3, respectively.
# This function prints all relations which have to be proven by hand to verify the
# following assertions:
# GrpRootHomF4(d2, t1)^(w1^2) = GrpRootHomF4(d2, -t1)
# GrpRootHomF4(d2, t1)^(w2^2) = GrpRootHomF4(d2, t1)
# GrpRootHomF4(d2, t1)^(w3^2) = GrpRootHomF4(d2, t1)
# GrpRootHomF4(d3, a1)^(w2^2) = GrpRootHomF4(d3, -a1)
# GrpRootHomF4(d3, a1)^(w2^2) = GrpRootHomF4(d3, a1)
# GrpRootHomF4(d3, a1)^(w2^2) = GrpRootHomF4(d3, -a1)
# In particular, w1^2, ..., w4^2 normalise the root groups U_d2 and U_d3
# Uses indeterminates t_1, a_1, t_(ComRing_rank), a_(ConicAlg_rank).
TestWeylSquareNormalise := function()
	local a, t, hom2, hom3;
	a := ConicAlgBasicIndet(1);
	t := ComRingBasicIndet(1);
	hom2 := x -> GrpRootHomF4(F4SimpleRoots[2], x);
	hom3 := x -> GrpRootHomF4(F4SimpleRoots[3], x);
	return TestWeylRelations([
		[[-1, -1, hom2(t), 1, 1], [hom2(-t)]],
		[[-2, -2, hom2(t), 2, 2], [hom2(t)]],
		[[-3, -3, hom2(t), 3, 3], [hom2(t)]],
		[[-2, -2, hom3(a), 2, 2], [hom3(-a)]],
		[[-3, -3, hom3(a), 3, 3], [hom3(a)]],
		[[-4, -4, hom3(a), 4, 4], [hom3(-a)]]
	]);
end;

# Denote by wi the standard Weyl element for F4SimpleRoots[i] by d2, d3 the simple
# roots of index 2 and 3, respectively.
# This function prints all relations which have to be proven by hand to verify the
# following assertions:
# - U_d2 is centralised by the following elements:
# -- w4
# -- w4^{w3*w2*w1}
# -- w([1,2,3,2,1,4,3,2,1,3,2,4,3,2,1])
# - U_d3 is centralised by the following elements:
# -- w1
# -- w2^{w3*w4}
# - w([4,3,2,1,3,2,3,4,3,2,1,3,2,3,4]) acts on U_d3 as ConicAlgInv.
TestStabNormalise := function()
	local a, t, hom2, hom3, stab21, stab22, stab23, stab31, stab32, stab33;
	a := ConicAlgBasicIndet(1);
	t := ComRingBasicIndet(1);
	hom2 := x -> GrpRootHomF4(F4SimpleRoots[2], x);
	hom3 := x -> GrpRootHomF4(F4SimpleRoots[3], x);
	# Reduced representations of generators of stabilizer of d2
	stab21 := [4]; # \sigma([0,1,1,0])
	stab22 := [-1, -2, -3, 4, 3, 2, 1]; # \sigma([0,-1,0,1])
	stab23 := [1,2,3,2,1,4,3,2,1,3,2,4,3,2,1]; # \sigma([0,0,0,-2])
	# Reduced representations of generators of stabilizer of d3
	stab31 := [1]; # \sigma([-1,-1,1,1])
	stab32 := [-4,-3,2,3,4]; # \sigma([0,0,-2,0])
	stab33 := [4,3,2,1,3,2,3,4,3,2,1,3,2,3,4]; # \sigma([0,0,1,-1])
	return TestWeylRelations([
		# [Concatenation(-Reversed(stab21), [hom2(t)], stab21), [hom2(t)]],
		# [Concatenation(-Reversed(stab22), [hom2(t)], stab22), [hom2(t)]],
		# [Concatenation(-Reversed(stab23), [hom2(t)], stab23), [hom2(t)]],
		# [Concatenation(-Reversed(stab31), [hom3(a)], stab31), [hom3(a)]],
		# [Concatenation(-Reversed(stab32), [hom3(a)], stab32), [hom3(a)]],
		[Concatenation(-Reversed(stab33), [hom3(a)], stab33), [hom3(ConicAlgInv(a))]]
	]);
end;