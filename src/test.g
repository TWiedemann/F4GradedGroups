### ---- Equality test ----

# Tests equality of two elements in the Lie algebra.
# If the output is true, they are equal.
# Otherwise they may or may not be equal.
# If print = true, additional information is printed for the parts which are not equal.
DeclareOperation("TestEquality", [IsLieElement, IsLieElement, IsBool]);
InstallMethod(TestEquality, [IsLieElement, IsLieElement, IsBool], function(lieEl1, lieEl2, print)
	local diff, isEqual, i, part;
	diff := Simplify(lieEl1 - lieEl2);
	isEqual := true;
	for i in [-2..2] do
		part := LiePart(diff, i);
		if not IsZero(part) and not IsZero(WithoutTraces(part)) then
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
			test := Simplify(lieEndo1(gen) - lieEndo2(gen));
			if not IsZero(test) and not IsZero(WithoutTraces(test)) then
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

# Same as TestEquality, but uses the inverted list of lie algebra generators
DeclareOperation("TestEqualityY", [IsLieEndo, IsLieEndo, IsInt, IsInt]);
DeclareOperation("TestEqualityY", [IsLieEndo, IsLieEndo, IsInt]);
DeclareOperation("TestEqualityY", [IsLieEndo, IsLieEndo]);

InstallMethod(TestEqualityY, [IsLieEndo, IsLieEndo, IsInt, IsInt],
	function(lieEndo1, lieEndo2, comIndetNum, conicIndetNum)
		local genList;
		genList := LieGensAsLie(comIndetNum, conicIndetNum, true);
		return TestEqualityOnGenList(lieEndo1, lieEndo2, genList);
	end
);

InstallMethod(TestEqualityY, [IsLieEndo, IsLieEndo, IsInt], 
	function(lieEndo1, lieEndo2, indetNum)
		return TestEquality(lieEndo1, lieEndo2, indetNum, indetNum);
	end
);

InstallMethod(TestEqualityY, [IsLieEndo, IsLieEndo], 
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

# relations: A list of lists [g1, g2] where g1, g2 are automorphisms of Lie
# Returns a list of all relations which have to be proven by hand to verify that g1 = g2 for
# all [g1, g2] \in relations.
# Uses indeterminates t_(ComRing_rank), a_(ConicAlg_rank).
TestRelations := function(relations)
	local rel, test, error, part, i, result;
	result := [];
	for rel in relations do
		test := TestEquality(rel[1], rel[2]);
		if test <> true then
			for error in test do
				# error[1] contains the Lie algebra generator on which rel[1] and rel[2]
				# differ, which is not interesting
				for i in [-2..2] do
					part := LiePart(error[2], i);
					if not IsZero(WithoutTraces(part)) then
						Add(result, part);
						# Display(part);
					fi;
				od;
			od;
		fi;
	od;
	return result;
end;

# Tests of specific mathematical behaviour

# Prints all terms that have to be proven to be zero to show that
# d(a[ij], b[jl]) = d(1[ij], ab[jl]) for a cyclic permutation i,j,l of 1,2,3
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

# Prints { a[ij], b[jl], . } for certain i, j, l
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

# Tests whether GrpRootHomF4(root, _) is a homomorphism.
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
# root: Element of F4. It is assumed that w is a Weyl element w.r.t. this root.
# onRootList: List of roots on which conjugation by w is tested.
# naive (optional): If true, then the naive root homomorphisms (i.e., no multiplication by gamma) are used.
# Output: A list [pars, errors] where:
# - pars is a list such that pars[i] is the parity of w on the root group with
# respect to onRootList[i].
# - errors is either true or a list consisting of lists [baseRoot, errorList] where
# baseRoot is a root and errorList is the list of Lie algebra elements which have to
# be proven to be zero.
# (To decide the parity, the sign with the shortest error list is chosen. There
# is no guarantee that this is the correct sign, but it normally works and will
# be tested by hand later.)
# Uses indeterminates a_1, t_1, a_{ConicAlg_rank}, t_{ComRing_rank}
_WeylErrorAndParity := function(root, onRootList, w, wInv, naive...)
	local baseRoot, baseRootErrorList, isWeylOnBaseRoot, errors, a, x, twistList,
		t, b, y, test, i, pars, par, parList;
	errors := [];
	pars := [];
	if Length(naive) = 0 then
		naive := false;
	else
		naive := naive[1];
	fi;
	for baseRoot in onRootList do
		if baseRoot in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
			x := GrpRootHomF4(baseRoot, a, naive);
			twistList := [a, -a, ConicAlgInv(a), -ConicAlgInv(a)];
			parList := [[1,1], [-1,1], [1,-1], [-1,-1]];
		else
			t := ComRingBasicIndet(1);
			x := GrpRootHomF4(baseRoot, t, naive);
			twistList := [t, -t];
			parList := [[1,1], [-1,1]];
		fi;
		isWeylOnBaseRoot := false;
		baseRootErrorList := fail;
		par := fail;
		for i in [1..Length(parList)] do
			b := twistList[i];
			y := GrpRootHomF4(F4Refl(baseRoot, root), b, naive);
			test := TestEquality(wInv*x*w, y);
			if test = true then
				isWeylOnBaseRoot := true;
				par := parList[i];
				break;
			elif baseRootErrorList = fail or Length(test) < Length(baseRootErrorList) then
				baseRootErrorList := test;
				par := parList[i];
			fi;
		od;
		Add(pars, par);
		if not isWeylOnBaseRoot then
			Add(errors, [baseRoot, List(baseRootErrorList, x -> x[2])]);
		fi;
	od;
	if IsEmpty(errors) then
		return [pars, true];
	else
		return [pars, errors];
	fi;
end;

WeylParityList := function(root, onRootList, w, wInv)
	return _WeylErrorAndParity(root, onRootList, w, wInv)[1];
end;

# w, wInv: Elements of LieEndo. It is assumed that wInv = w^-1.
# root: Element of F4. It is assumed that w is a Weyl element w.r.t. this root.
# parList: A list with 48 entries of the form [+-1, +-1]
# Output: true if w can be proven to be a root-Weyl element with parity list parList.
# Otherwise the output is a list consisting of lists [baseRoot, errorList] where
# baseRoot is a root and errorList is the list of Lie algebra elements which have to
# be proven to be zero.
# Uses indeterminates a_1, t_1, a_{ConicAlg_rank}, t_{ComRing_rank}
# Currently obsolete
TestWeylParity := function(root, w, wInv, parList)
	local baseRoot, errors, a, x, b, y, test, i, par;
	errors := [];
	for i in [1..Length(F4Roots)] do
		baseRoot := F4Roots[i];
		par := parList[i];
		if baseRoot in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
			x := GrpRootHomF4(baseRoot, a);
		else
			a := ComRingBasicIndet(1);
			x := GrpRootHomF4(baseRoot, a);
		fi;
		# b is a twisted by par
		b := a;
		if par[1] = -1 then
			b := -b;
		fi;
		if par[2] = -1 then
			b := ConicAlgInv(b);
		fi;
		y := GrpRootHomF4(F4Refl(baseRoot, root), b);
		test := TestEquality(wInv*x*w, y);
		if test <> true then
			Add(errors, [baseRoot, List(test, x -> x[2])]);
		fi;
	od;
	if IsEmpty(errors) then
		return true;
	else
		return errors;
	fi;
end;

# Documentation: See TestWeyl, but with onRootList
TestWeylOn := function(root, onRootList, w, wInv, naive)
	return _WeylErrorAndParity(root, onRootList, w, wInv, naive)[2];
end;

# w, wInv: Elements of LieEndo. It is assumed that wInv = w^-1.
# Output: true if w can be proven to be a root-Weyl element.
# Otherwise the output is a list consisting of lists [baseRoot, errorList] where
# baseRoot is a root and errorList is the list of Lie algebra elements which have to
# be proven to be zero.
# Uses indeterminates a_1, t_1, a_{ConicAlg_rank}, t_{ComRing_rank}
TestWeyl := function(root, w, wInv, naive...)
	if Length(naive) = 0 then
		naive := false;
	else
		naive := naive[1];
	fi;
	return TestWeylOn(root, F4Roots, w, wInv, naive);
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

# Returns a list of relations which have to be verified by hand to prove that
# the parities of GrpStandardWeylF4(F4SimpleRoots[i]) adhere to F4ParityList
TestStandardWeylParity := function(i)
	local d, w, wInv, errorList, error, j, baseRoot, a, x, b, y;
	d := F4SimpleRoots[i];
	w := GrpStandardWeylF4(d);
	wInv := GrpStandardWeylInvF4(d);
	errorList := [];
	for j in [1..Length(F4Roots)] do
		baseRoot := F4Roots[j];
		if baseRoot in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
		else
			a := ComRingBasicIndet(1);
		fi;
		x := GrpRootHomF4(baseRoot, a);
		b := a;
		if F4ParityList[j][i][1] = -1 then
			b := -b;
		fi;
		if F4ParityList[j][i][2] = -1 then
			b := ConicAlgInv(b);
		fi;
		y := GrpRootHomF4(F4Refl(baseRoot, d), b);
		error := TestRelations([[wInv*x*w, y]]);
		if not IsEmpty(error) then
			Print(baseRoot, " -> ", F4Refl(baseRoot, d), ":\n");
			Display(error);
			errorList := Concatenation(errorList, error);
		fi;
	od;
	return errorList;
end;

GrpRootHomCom := function(root1, a1, root2, a2, naive...)
	local hom;
	if Length(naive) = 0 then
		naive := false;
	else
		naive := naive[1];
	fi;
	hom := function(root, a)
		return GrpRootHomF4(root, a, naive);
	end;
	return hom(root1, -a1)*hom(root2, -a2)*hom(root1, a1)*hom(root2, a2);
end;

# Returns a list of all relations which have to be verified by hand to prove that
# all desired commutator relations are satisfied.
TestComRels := function(naive...)
	local t1, t2, a1, a2, d1, d2, d3, d4, g1, g2, g3, comm, test, rel;
	if Length(naive) = 0 then
		naive := false;
	else
		naive := naive[1];
	fi;
	t1 := ComRingBasicIndet(1);
	t2 := ComRingBasicIndet(2);
	a1 := ConicAlgBasicIndet(1);
	a2 := ConicAlgBasicIndet(2);
	d1 := F4SimpleRoots[1];
	d2 := F4SimpleRoots[2];
	d3 := F4SimpleRoots[3];
	d4 := F4SimpleRoots[4];
	g1 := ComRingGamIndet(1);
	g2 := ComRingGamIndet(2);
	g3 := ComRingGamIndet(3);
	if not naive then
		return TestRelations([
			# Commutator relation on [d1, d2]
			[GrpRootHomCom(d1, t1, d2, t2), GrpRootHomF4(d1+d2, t1*t2)],
			# Commutator relation on [d2, d3]
			[
				GrpRootHomCom(d2, t1, d3, a1),
				GrpRootHomF4(d2+d3, -t1*a1) * GrpRootHomF4(d2+2*d3, t1*ConicAlgNorm(a1))
			],
			# Commutator relation on [d2+d3, d3]
			[
				GrpRootHomCom(d2+d3, a1, d3, a2),
				GrpRootHomF4(d2+2*d3, -ConicAlgNormLin(ConicAlgInv(a1), ConicAlgInv(a2)))
			],
			# Commutator relation on [d3, d4]
			[GrpRootHomCom(d3, a1, d4, a2), GrpRootHomF4(d3+d4, -ConicAlgInv(a1)*ConicAlgInv(a2))]
		]);
	else
		return TestRelations([
			[
				GrpRootHomCom(d2, t1, d3, a1, true),
				GrpRootHomF4(d2+d3, -t1*a1, true) * GrpRootHomF4(d2+2*d3, g2*g3*t1*ConicAlgNorm(a1), true)
			]
		]);
	fi;
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
		if Simplify(h*x - coeff*x) <> LieZero then
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

# Tests whether GrpRootHomF4NonDiv and GrpRootHomF4Div coincide on root
# Uses indeterminates a_1, a_{ConicAlg_rank-1}, a_{ConicAlg_rank}, t_1, t_{ComRing_rank}
TestGrpRootHomExp := function(root)
	local a;
	if root in F4ShortRoots then
		a := ConicAlgBasicIndet(1);
	elif root in F4LongRoots then
		a := ComRingBasicIndet(1);
	fi;
	return TestEqualityOnModuleGens(GrpRootHomF4Div(root, a), GrpRootHomF4NonDiv(root, a));
end;

TestAllGrpRootHomExp := function()
	local root, test;
	for root in F4Roots do
		if F4RootG2Coord(root) <> [0,0] then
			test := TestGrpRootHomExp(root);
			if test <> true then
				Print("Problem for ", root, "\n");
				return test;
			fi;
		fi;
	od;
	return true;
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

# Returns true if the content of _ComRingIndetInfo is correct
TestComRingIndetInfo := function()
	local i, info, type, indet;
	for i in [1..Length(_ComRingIndetInfo)] do
		info := _ComRingIndetInfo[i];
		type := info[1];
		info := info[2];
		indet := Indeterminate(BaseRing, i);
		if (type = "t" and indet <> ComRingBasicIndet(info))
			or (type = "g" and indet <> ComRingGamIndet(info))
			or (type = "n" and indet <> ConicAlgMagNorm(info))
			or (type = "tr" and indet <> ConicAlgMagTr(info)) then
			return i;
		fi;
	od;
	return true;
end;

