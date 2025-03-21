### ---- Equality test ----

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
				Display("No proven equality for:");
				Display(lieEl1);
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