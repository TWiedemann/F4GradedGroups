### ---- Equality test ----

# Tests equality of two elements in the Lie algebra.
# If the output is true, they are equal.
# Otherwise they may or may not be equal.
# If print = true, additional information is printed for the parts which are not equal.
DeclareOperation("TestEquality", [IsLieElement, IsLieElement, IsBool]);
InstallMethod(TestEquality, [IsLieElement, IsLieElement, IsBool], function(lieEl1, lieEl2, print)
	local diff, isEqual, i, part;
	diff := lieEl1 - lieEl2;
	isEqual := true;
	for i in [-2..2] do
		part := LiePart(diff, i);
		if i = 0 then
			part := ApplyDistAndPeirceLaw(part);
		fi;
		if not IsZero(part) then
			isEqual := false;
			if print then
				Print(String(i), " part: ", part, "\n");
			fi;
		fi;
	od;
	return isEqual;
end);

# lieEndo1, lieEndo2: Elements of LieEndo
# genList: List of elements of Lie
# Output: true if lieEndo1 and lieEndo2 agree on all elements of genList.
# Otherwise the output is the list of all lists [a, b] where a is an element of genList
# algebra and b = lieEndo1(a) - lieEndo2(a) <> 0.
DeclareOperation("TestEqualityOnGenList", [IsLieEndo, IsLieEndo, IsList]);
InstallMethod(TestEqualityOnGenList, [IsLieEndo, IsLieEndo, IsList], 
	function(lieEndo1, lieEndo2, genList)
		local gen, test, errorList;
		errorList := [];
		for gen in genList do
			test := ApplyDistAndPeirceLaw(lieEndo1(gen) - lieEndo2(gen));
			if not IsZero(test) then
				Add(errorList, [gen, test]);
			fi;
		od;
		if IsEmpty(errorList) then
			return true;
		else
			return errorList;
		fi;
	end
);

# TestEquality(f, g, comIndetNum, conicIndetNum) calls
# TestEqualityOnGenList(f, g, LieGensAsLie(comIndetNum, conicIndetNum)).
# If only one integer n is provided, then TestEquality(f, g, n, n) is called.
# If no integer is provided, then TestEquality(f, g, ComRing_rank, ConicAlg_rank)
# is called.
# Uses indeterminates t_comIndetNum and a_conicIndetNum
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsInt, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo]);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsInt, IsInt],
	function(lieEndo1, lieEndo2, comIndetNum, conicIndetNum)
		local genList;
		genList := LieGensAsLie(comIndetNum, conicIndetNum);
		return TestEqualityOnGenList(lieEndo1, lieEndo2, genList);
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsInt], 
	function(lieEndo1, lieEndo2, indetNum)
		return TestEquality(lieEndo1, lieEndo2, indetNum, indetNum);
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo], 
	function(lieEndo1, lieEndo2)
		return TestEquality(lieEndo1, lieEndo2, ComRing_rank, ConicAlg_rank);
	end
);

# Like TestEquality, but uses LieGensAsModule in place of LieGensAsLie.
# Uses indeterminates t_comIndetNum, a_conicIndetNum AND a_{conicIndetNum+1}
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo, IsInt, IsInt]);
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo, IsInt]);
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo]);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo, IsInt, IsInt],
	function(lieEndo1, lieEndo2, comIndetNum, conicIndetNum)
		local genList;
		genList := LieGensAsModule(comIndetNum, conicIndetNum);
		return TestEqualityOnGenList(lieEndo1, lieEndo2, genList);
	end
);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo, IsInt], 
	function(lieEndo1, lieEndo2, indetNum)
		return TestEqualityOnModuleGens(lieEndo1, lieEndo2, indetNum, indetNum);
	end
);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo], 
	function(lieEndo1, lieEndo2)
		return TestEqualityOnModuleGens(lieEndo1, lieEndo2, ComRing_rank, ConicAlg_rank-1);
	end
);

# Tests of specific mathematical behaviour

TestDDRelation := function()
	local i, j, l, a1, a2, a3, t, f, gen, a;
	i := 1;
	j := 2;
	l := 3;
	a1 := ConicAlgBasicIndet(1);
	a2 := ConicAlgBasicIndet(2);
	a3 := ConicAlgBasicIndet(3);
	t := ComRingBasicIndet(1);
	f := L0dd(CubicAlgElMat(i, j, a1), CubicAlgElMat(j, l, a2))
			- L0dd(CubicAlgElMat(i, j, One(ConicAlg)), CubicAlgElMat(j, l, a1*a2));
	for gen in BrownGensAsModule(4) do
		a := L0AsEndo(f, 1)(gen);
		if not IsZero(a) then
			Display(gen);
			Display(a);
		fi;
	od;
end;

TestDRelation := function()
	local indices, list, i, j, l, a, x, b, y, cubicGeneric;
	indices := [[1,1,2], [1,2,2], [1,3,2], [2,1,1], [2,2,1], [2,3,1]];
	for list in indices do
		i := list[1];
		j := list[2];
		l := list[3];
		if i = j then
			a := ComRingBasicIndet(4);
			x := CubicComEl(i, a);
		else
			a := ConicAlgBasicIndet(4);
			x := CubicAlgElMat(i, j, a);
		fi;
		if j = l then
			b := ComRingBasicIndet(5);
			y := CubicComEl(j, b);
		else
			b := ConicAlgBasicIndet(5);
			y := CubicAlgElMat(j, l, b);
		fi;
		cubicGeneric := CubicGenericEl(0);
		Display(list);
		Display(JordanD(x, y, cubicGeneric));
	od;
end;

# Tests whether GrpRootHomF4(root, _) is a homomorphisms.
# If root is short: Uses indeterminates a_1, a_2, a_(ConicAlg_rank), t_(ComRing_rank),
# and it is assumed that ConicAlg_rank > 2.
# If root is long: Uses indeterminates t_1, t_2, t_(ComRing_rank), a_(ConicAlg_rank),
# and it is assumed that ComRing_rank > 2.
TestGrpRootHom := function(root)
	local x1, x2, g1, g2, g3;
	if root in F4ShortRoots then
		x1 := ConicAlgBasicIndet(1);
		x2 := ConicAlgBasicIndet(2);
	elif root in F4LongRoots then
		x1 := ComRingBasicIndet(1);
		x2 := ComRingBasicIndet(2);
	else
		return fail;
	fi;
	g1 := GrpRootHomF4(root, x1);
	g2 := GrpRootHomF4(root, x2);
	g3 := GrpRootHomF4(root, x1+x2);
	return TestEquality(g1*g2, g3, true);
end;

# Tests whether GrpRootHomF4 is a homomorphism for all roots.
# Uses indeterminates a_1, a_2, t_1, t_2, a_(ConicAlg_rank), t_(ComRing_rank),
# and it is assumed that ComRing_rank > 2 and ConicAlg_rank > 2.
TestGrpRootHoms := function()
	local isHom, root;
	isHom := true;
	for root in F4Roots do
		if not TestGrpRootHom(root) then
			isHom := false;
		fi;
	od;
	return isHom;
end;

# w, wInv: Elements of LieEndo. It is assumed that wInv = w^-1.
# Output: true if w can be proven to be a root-Weyl element.
# Otherwise the output is a list consisting of lists [baseRoot, errorList] where
# baseRoot is a root and errorList is the list of Lie algebra elements which have to
# be proven to be zero.
# Uses indeterminates a_1, t_1, a_{ConicAlg_rank}, t_{ComRing_rank}
TestWeyl := function(root, w, wInv)
	local baseRoot, baseRootErrorList, isWeylOnBaseRoot, errorList, a, x, twistList, t, b, y, test;
	errorList := [];
	for baseRoot in F4Roots do
		if baseRoot in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
			x := GrpRootHomF4(baseRoot, a);
			twistList := [a, -a, ConicAlgInv(a), -ConicAlgInv(a)];
		else
			t := ComRingBasicIndet(1);
			x := GrpRootHomF4(baseRoot, t);
			twistList := [t, -t];
		fi;
		isWeylOnBaseRoot := false;
		baseRootErrorList := fail;
		for b in twistList do
			y := GrpRootHomF4(F4Refl(baseRoot, root), b);
			test := TestEquality(wInv*x*w, y);
			if test = true then
				isWeylOnBaseRoot := true;
				break;
			elif baseRootErrorList = fail or Length(test) < Length(baseRootErrorList) then
				baseRootErrorList := test;
			fi;
		od;
		if not isWeylOnBaseRoot then
			Add(errorList, [baseRoot, List(baseRootErrorList, x -> x[2])]);
		fi;
	od;
	if IsEmpty(errorList) then
		return true;
	else
		return errorList;
	fi;
end;


# root: Root in F4.
# Returns true if GrpWeylF4(root, one, -one) can be proven to be a Weyl element,
# otherwise false.
# Uses indeterminates a_1, t_1, a_{ConicAlg_rank}, t_{ComRing_rank}
TestWeylStandard := function(root)
	local w, wInv;
	w := GrpStandardWeylF4(root);
	wInv := GrpStandardWeylInvF4(root);
	return TestWeyl(root, w, wInv);
end;

TestLongWeyl := function()
	local root, testResult, i;
	testResult := [];
	for i in [1..Length(F4PosLongRoots)] do
		root := F4PosLongRoots[i];
		Print(i, "/", Length(F4PosLongRoots), "\n");
		Add(testResult, [root, TestWeylStandard(root)]);
	od;
	return testResult;
end;

TestShortWeyl := function()
	local root, testResult, i;
	testResult := [];
	for i in [1..Length(F4PosShortRoots)] do
		root := F4PosShortRoots[i];
		Print(i, "/", Length(F4PosShortRoots), "\n");
		Add(testResult, [root, TestWeylStandard(root)]);
	od;
	return testResult;
end;

GrpRootHomComm := function(root1, root2, param1, param2)
	return GrpRootHomF4(root1, -param1) * GrpRootHomF4(root2, -param2)
		* GrpRootHomF4(root1, param1) * GrpRootHomF4(root2, param2);
end;

# Returns true if c(root1, root2) = -c(-root1, -root2) for all roots root1, root2 in F4
# where c = ChevStrucConst
TestChevStrucConstSigns := function()
	local i, j, root1, root2;
	for i in [1..Length(F4Roots)] do
		for j in [1..Length(F4Roots)] do
			# (It would be sufficient to test only the cases with i<j, but the
			# whole test runs in less than a minute anyway.)
			root1 := F4Roots[i];
			root2 := F4Roots[j];
			if ChevStrucConst(root1, root2) <> -ChevStrucConst(-root1, -root2) then
				return false;
			fi;
		od;
	od;
	return true;
end;

# root: Root in F4.
# Output: true if ChevHEl(root) acts as the scalar F4CartanInt(alpha, root)
# on every root space L_alpha of Lie, and false otherwise
TestChevHOnRoot := function(root)
	local h, alpha, a, x, coeff;
	h := ChevHEl(root);
	for alpha in F4Roots do
		if alpha in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
		else
			a := ComRingBasicIndet(1);
		fi;
		x := LieRootHomF4(alpha, a);
		coeff := F4CartanInt(alpha, root) * One(ComRing);
		if ApplyDistAndPeirceLaw(h*x - coeff*x) <> LieZero then
			return false;
		fi;
	od;
	return true;
end;

# Returns true if TestChevHOnRoot(alpha) = true for all alpha \in F4
TestChevH := function()
	local root;
	for root in F4Roots do
		if TestChevHOnRoot(root) = false then
			return false;
		fi;
	od;
	return true;
end;

# relations: A list of lists [g1, g2] where g1, g2 are automorphisms of Lie
# Prints all relations which have to be proven by hand to verify that g1 = g2 for
# all [g1, g2] \in relations.
# Uses indeterminates t_(ComRing_rank), a_(ConicAlg_rank).
TestRelations := function(relations)
	local rel, test, error, part, i;
	for rel in relations do
		test := TestEquality(rel[1], rel[2]);
		if test <> true then
			for error in test do
				# error[1] contains the Lie algebra generator on which rel[1] and rel[2]
				# differ, which is not interesting
				for i in [-2..2] do
					part := LiePart(error[2], i);
					if not IsZero(part) then
						Display(part);
					fi;
				od;
			od;
		fi;
	od;
end;

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
	TestRelations(weylRelations);
end;

# Prints all relations which have to be proven by hand to verify the braid relations for
# the standard Weyl elements w.r.t. F4SimpleRoots.
# Uses indeterminates a_1, t_1
TestBraidRel := function()
	TestWeylRelations([
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
	TestWeylRelations([
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
	TestWeylRelations([
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
	TestWeylRelations([
		[Concatenation(-Reversed(stab21), [hom2(t)], stab21), [hom2(t)]],
		[Concatenation(-Reversed(stab22), [hom2(t)], stab22), [hom2(t)]],
		[Concatenation(-Reversed(stab23), [hom2(t)], stab23), [hom2(t)]],
		[Concatenation(-Reversed(stab31), [hom3(a)], stab31), [hom3(a)]],
		[Concatenation(-Reversed(stab32), [hom3(a)], stab32), [hom3(a)]],
		[Concatenation(-Reversed(stab33), [hom3(a)], stab33), [hom3(ConicAlgInv(a))]]
	]);
end;

TestGrpRootHomExp := function(root)
	local a;
	if root in F4ShortRoots then
		a := ConicAlgBasicIndet(1);
	elif root in F4LongRoots then
		a := ComRingBasicIndet(1);
	fi;
	return TestEqualityOnModuleGens(GrpRootHomF4(root, a), GrpRootHomF4NonDiv(root, a));
end;

# Uses indeterminates t_1, t_2, a_1, ..., a_4
DeclareOperation("LieEndoIsAuto", [IsLieEndo]);
InstallMethod(LieEndoIsAuto, [IsLieEndo], function(f)
	local lieGens1, lieGens2, isAuto, lieEl1, lieEl2, counter, total, test;
	lieGens1 := LieGensAsModule(1, 1);
	lieGens2 := LieGensAsModule(2, 3);
	isAuto := true;
	counter := 1;
	total := Length(lieGens1);
	for lieEl1 in lieGens1 do
		Print("Progress: ", counter, "/", total, "\n");
		for lieEl2 in lieGens2 do
			test := TestEquality(f(lieEl1 * lieEl2), f(lieEl1) * f(lieEl2), false);
			if not test then
				isAuto := false;
				Display("No proven equality f([a,b]) = [f(a), f(b)] for:");
				Display("a:");
				Display(lieEl1);
				Display("b:");
				Display(lieEl2);
				Display("Problem:");
				# Test equality again with error message - not efficient, but
				# a single equality test is not too expensive.
				TestEquality(f(lieEl1 * lieEl2), f(lieEl1) * f(lieEl2), true);
			fi;
		od;
		counter := counter + 1;
	od;
	return isAuto;
end);

TestGrpRootHomIsAutoLongFromList := function(list)
	local result, root, x, isAuto, i;
	result := [];
	for i in list do
		root := F4LongRoots[i];
		Display(root);
		x := GrpRootHomF4(root, ComRingBasicIndet(3));
		isAuto := LieEndoIsAuto(x);
		Display(isAuto);
		Add(result, [root, isAuto]);
	od;
	return result;
end;

TestGrpRootHomIsAutoLong := function()
	return TestGrpRootHomIsAutoLongFromList([1..Length(F4LongRoots)]);
end;

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