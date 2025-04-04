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


# Tests equality of two elements in the Lie algebra.
# If the output is true, they are equal.
# Otherwise they may or may not be equal.
# If two integers comIndetNum and conicIndetNum are provided, they are used
# as the indeterminates numbers for the generators of Lie in the test.
# If only one integer is provided, it is used for both indeterminates numbers.
# If no integer is provided, we use ConicAlg_rank and ComRing_rank.
# If print = true, additional information is printed for the parts which are not equal.
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsBool, IsInt, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsBool, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsBool]);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsBool, IsInt, IsInt],
	function(lieEndo1, lieEndo2, print, comIndetNum, conicIndetNum)
		local gens, gen, isEqual;
		gens := LieGensAsLie(comIndetNum, conicIndetNum);
		isEqual := true;
		for gen in gens do
			if not TestEquality(lieEndo1(gen), lieEndo2(gen), print) then
				isEqual := false;
			fi;
		od;
		return isEqual;
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsBool, IsInt], 
	function(lieEndo1, lieEndo2, print, indetNum)
		return TestEquality(lieEndo1,lieEndo2, print, indetNum, indetNum);
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsBool], 
	function(lieEndo1, lieEndo2, print)
		return TestEquality(lieEndo1,lieEndo2, print, ComRing_rank, ConicAlg_rank);
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

# root: Root in F4.
# Returns true if GrpWeylOneF4(root) can be proven to be a Weyl element,
# otherwise false.
TestWeyl := function(root)
	local w, wInv, root2, a, x, twistList, t, isWeyl, b, y;
	w := GrpWeylOneF4(root);
	wInv := GrpWeylOneInvF4(root);
	for root2 in F4Roots do
		if root2 in F4ShortRoots then
			a := ConicAlgBasicIndet(1);
			x := GrpRootHomF4(root2, a);
			twistList := [a, -a, ConicAlgInv(a), -ConicAlgInv(a)];
		else
			t := ComRingBasicIndet(1);
			x := GrpRootHomF4(root2, t);
			twistList := [t, -t];
		fi;
		isWeyl := false;
		for b in twistList do
			y := GrpRootHomF4(F4Refl(root, root2), b);
			if TestEquality(wInv*x*w, y, false) then
				isWeyl := true;
				break;
			fi;
			if not isWeyl then
				Print("Not a Weyl element on root group ", root2, "\n");
				return false;
			fi;
		od;
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