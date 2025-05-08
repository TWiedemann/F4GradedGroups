LieZeroString := "0_L";
LieNeg2String := "x";
LiePos2String := "y";

# rep: Internal representation of an element of L
# Output: A string representing this element
LieRepToString := function(rep)
	local stringList, name, s;
	stringList := [];
	for name in ["neg2", "neg1", "zero", "pos1", "pos2"] do
		if not IsZero(rep.(name)) then
			s := String(rep.(name));
			if name = "neg2" then
				s := Concatenation("(", s, ")*", LieNeg2String);
			elif name = "pos2" then
				s := Concatenation("(", s, ")*", LiePos2String);
			elif name = "pos1" then
				s := Concatenation(s, "_+");
			elif name = "neg1" then
				s := Concatenation(s, "_-");
			fi;
			Add(stringList, s);
		fi;
	od;
	return StringSum(stringList, " + ", LieZeroString);
end;

## Define Lie bracket for all combinations of components
DeclareOperation("LieBracketBrownPosPos", [IsBrownElement, IsBrownElement]);
DeclareOperation("LieBracketBrownNegPos", [IsBrownElement, IsBrownElement]);

# brown1, brown2: Element of Brown, regarded as element of L_1.
# Output: a in ComRing such that [brown1, brown2] = a * LieY.
# If brown1, brown2 are regarded as elements of L_{-1}, the output a satisfies
# that [brown1, brown2] = a * LieX.
InstallMethod(LieBracketBrownPosPos, [IsBrownElement, IsBrownElement], function(brown1, brown2)
	local lam, b1, b2, mu, nu, c1, c2, rho;
	# Introduce notation of [DMW, 3.18]
	lam := BrownElPart(brown1, 1);
	b1 := BrownElPart(brown1, 2);
	b2 := BrownElPart(brown1, 3);
	mu := BrownElPart(brown1, 4);
	nu := BrownElPart(brown2, 1);
	c1 := BrownElPart(brown2, 2);
	c2 := BrownElPart(brown2, 3);
	rho := BrownElPart(brown2, 4);
	return CubicBiTr(b1, c2) - CubicBiTr(c1, b2) + mu*nu - lam*rho;
end);

# brown1: Element of Brown, regarded as element of L_{-1}
# brown2: Element of Brown, regarded as element of L_1
# Output: [brown1, brown2] (in L0)
InstallMethod(LieBracketBrownNegPos, [IsBrownElement, IsBrownElement], function(brown1, brown2)
	local lam, b1, b2, mu, nu, c1, c2, rho;
	# Introduce notation of [DMW, 3.18]
	lam := BrownElPart(brown1, 1);
	b1 := BrownElPart(brown1, 2);
	b2 := BrownElPart(brown1, 3);
	mu := BrownElPart(brown1, 4);
	nu := BrownElPart(brown2, 1);
	c1 := BrownElPart(brown2, 2);
	c2 := BrownElPart(brown2, 3);
	rho := BrownElPart(brown2, 4);
	return CubicNegToL0Emb(-lam*c2 + CubicCross(b1, c1) - nu*b2)
			+ ((lam*rho - CubicBiTr(b1, c2)) * L0Zeta
				+ (CubicBiTr(c1, b2) - mu*nu) * (L0Xi - L0Zeta)
				+ L0dd(b1, c2) + L0dd(c1, b2))
			+ CubicPosToL0Emb(-rho*b1 + CubicCross(b2, c2) - mu*c1);
end);

# Elements of L are represented by records with entries "neg2" (in ComRing),
# "neg1" (in Brown), "zero" (in L0), "pos1" (in Brown) and "pos2" (in ComRing).
LieSpec := rec(
	ElementName := "LieElement",
	Addition := function(a, b)
		return rec(
			neg2 := a.neg2 + b.neg2,
			neg1 := a.neg1 + b.neg1,
			zero := a.zero + b.zero,
			pos1 := a.pos1 + b.pos1,
			pos2 := a.pos2 + b.pos2
		);
	end,
	Zero := a -> rec(
		neg2 := Zero(ComRing),
		neg1 := BrownZero,
		zero := L0Zero,
		pos1 := BrownZero,
		pos2 := Zero(ComRing)
	),
	AdditiveInverse := function(a)
		return rec(
			neg2 := -a.neg2,
			neg1 := -a.neg1,
			zero := -a.zero,
			pos1 := -a.pos1,
			pos2 := -a.pos2
		);
	end,
	Print := function(a)
		Print(LieRepToString(a));
	end,
	Multiplication := function(a, b)
		local neg2, neg1, zero, pos1, pos2;
		# Initialisation of the components of [a, b]
		neg2 := Zero(ComRing);
		neg1 := BrownZero;
		zero := L0Zero;
		pos1 := BrownZero;
		pos2 := Zero(ComRing);
		# [a.neg2, b]
		neg2 := neg2 - L0AsEndo(b.zero, -2)(a.neg2); # [a.neg2, b.zero]
		neg1 := neg1 - a.neg2*b.pos1; # [a.neg2, b.pos1];
		zero := zero + a.neg2*b.pos2*L0Xi; # [a.neg2, b.pos2]
		# [a.neg1, b]
		neg2 := neg2 + LieBracketBrownPosPos(a.neg1, b.neg1); # [a.neg1, b.neg1]
		neg1 := neg1 - L0AsEndo(b.zero, -1)(a.neg1); # [a.neg1, b.zero]
		zero := zero + LieBracketBrownNegPos(a.neg1, b.pos1); # [a.neg1, b.pos1]
		pos1 := pos1 - b.pos2 * a.neg1; # [a.neg1, b.pos2]
		# [a.zero, b]
		neg2 := neg2 + L0AsEndo(a.zero, -2)(b.neg2); # [a.zero, b.neg2]
		neg1 := neg1 + L0AsEndo(a.zero, -1)(b.neg1); # [a.zero, b.neg1]
		zero := zero + a.zero*b.zero; # [a.zero, b.zero]
		pos1 := pos1 + L0AsEndo(a.zero, 1)(b.pos1); # [a.zero, b.pos1]
		pos2 := pos2 + L0AsEndo(a.zero, 2)(b.pos2); # [a.zero, b.pos2]
		# [a.pos1, b]
		neg1 := neg1 + b.neg2 * a.pos1; # [a.pos1, b.neg2]
		zero := zero - LieBracketBrownNegPos(b.neg1, a.pos1); # [a.pos1, b.neg1]
		pos1 := pos1 - L0AsEndo(b.zero, 1)(a.pos1); # [a.pos1, b.zero]
		pos2 := pos2 + LieBracketBrownPosPos(a.pos1, b.pos1); # [a.pos1, b.pos1]
		# [a.pos2, b]
		zero := zero - a.pos2*b.neg2*L0Xi; # [a.pos2, b.neg2]
		pos1 := pos1 + a.pos2*b.neg1; # [a.pos2, b.neg1]
		pos2 := pos2 - L0AsEndo(b.zero, 2)(a.pos2); # [a.pos2, b.zero]
		return rec(
			neg2 := neg2,
			neg1 := neg1,
			zero := zero,
			pos1 := pos1,
			pos2 := pos2
		);
	end,
	MathInfo := IsAdditivelyCommutativeElement
);

Lie := ArithmeticElementCreator(LieSpec);

## Constructors and embeddings for elements of Lie
LieZero := Lie(LieSpec.Zero(fail));

DeclareOperation("LieElFromTuple", [IsRingElement, IsBrownElement, IsL0Element,
		IsBrownElement, IsRingElement]);
InstallMethod(LieElFromTuple, [IsRingElement, IsBrownElement, IsL0Element,
	IsBrownElement, IsRingElement],
	function(neg2, neg1, zero, pos1, pos2)
		ReqComRingEl([neg2, pos2]);
		return Lie(rec(
			neg2 := neg2,
			neg1 := neg1,
			zero := zero,
			pos1 := pos1,
			pos2 := pos2
		));
	end
);

LieX := LieElFromTuple(One(ComRing), BrownZero, L0Zero, BrownZero, Zero(ComRing));
LieY := LieElFromTuple(Zero(ComRing), BrownZero, L0Zero, BrownZero, One(ComRing));

DeclareOperation("DDToLieEmb", [IsDDElement]);
DeclareOperation("L0ToLieEmb", [IsL0Element]);
DeclareOperation("BrownPosToLieEmb", [IsBrownElement]);
DeclareOperation("BrownNegToLieEmb", [IsBrownElement]);
DeclareOperation("CubicPosToLieEmb", [IsCubicElement]);
DeclareOperation("CubicNegToLieEmb", [IsCubicElement]);

InstallMethod(L0ToLieEmb, [IsL0Element], function(L0el)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0el, BrownZero, Zero(ComRing));
end);

InstallMethod(DDToLieEmb, [IsDDElement], x -> L0ToLieEmb(DDToL0Emb(x)));

InstallMethod(BrownPosToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0Zero, brownEl, Zero(ComRing));
end);

InstallMethod(BrownNegToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), brownEl, L0Zero, BrownZero, Zero(ComRing));
end);

InstallMethod(CubicPosToLieEmb, [IsCubicElement], function(cubicEl)
	return L0ToLieEmb(CubicPosToL0Emb(cubicEl));
end);

InstallMethod(CubicNegToLieEmb, [IsCubicElement], function(cubicEl)
	return L0ToLieEmb(CubicNegToL0Emb(cubicEl));
end);

DeclareOperation("Liedd", [IsCubicElement, IsCubicElement]);
InstallMethod(Liedd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	return L0ToLieEmb(L0dd(cubicEl1, cubicEl2));
end);

LieZeta := L0ToLieEmb(L0Zeta);
LieXi := L0ToLieEmb(L0Xi);

## Getters for components

DeclareOperation("LiePart", [IsLieElement, IsInt]);
InstallMethod(LiePart, [IsLieElement, IsInt], function(lieEl, i)
	if i = -2 then
		return UnderlyingElement(lieEl).neg2;
	elif i = -1 then
		return UnderlyingElement(lieEl).neg1;
	elif i = 0 then
		return UnderlyingElement(lieEl).zero;
	elif i = 1 then
		return UnderlyingElement(lieEl).pos1;
	elif i = 2 then
		return UnderlyingElement(lieEl).pos2;
	else
		Error("LiePart: Invalid position");
		return fail;
	fi;
end);

InstallOtherMethod(IsZero, [IsLieElement], function(lieEl)
	local i;
	for i in [-2..2] do
		if not IsZero(LiePart(lieEl, i)) then
			return false;
		fi;
	od;
	return true;
end);

## Display and String

InstallMethod(String, [IsLieElement], x -> LieRepToString(UnderlyingElement(x)));

InstallMethod(Display, [IsLieElement], function(lieEl)
	local i;
	for i in [-2..2] do
		if i >= 0 then
			Print(" ");
		fi;
		Print(String(i), " part: ", String(LiePart(lieEl, i)), "\n");
	od;
end);

## Scalar multiplication ComRing x Lie -> Lie
InstallOtherMethod(\*, "for ComRingElement and LieElement", [IsRingElement, IsLieElement], 2, function(comEl, lieEl)
	return Lie(rec(
		neg2 := comEl * LiePart(lieEl, -2),
		neg1 := comEl * LiePart(lieEl, -1),
		zero := comEl * LiePart(lieEl, 0),
		pos1 := comEl * LiePart(lieEl, 1),
		pos2 := comEl * LiePart(lieEl, 2)
	));
end);

## ---- Simplifier ----

# lieEl: Element of Lie.
# Output: The same element with ApplyDistAndPeirceLaw applied to the DD-part.
DeclareOperation("ApplyDistAndPeirceLaw", [IsLieElement]);
InstallMethod(ApplyDistAndPeirceLaw, [IsLieElement], function(lieEl)
	local rep;
	rep := StructuralCopy(UnderlyingElement(lieEl));
	rep.zero := ApplyDistAndPeirceLaw(rep.zero);
	return Lie(rep);
end);

### Root homomorphisms

DeclareOperation("LieRootHomF4", [IsList, IsRingElement]);

InstallMethod(LieRootHomF4, [IsList, IsRingElement], function(root, a)
	local sum, G2Root, minusSignRootsLong, minusSignRootsShort;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
	# Add minus signs to ensure that elements w(1, -1) are Weyl elements
	minusSignRootsLong := Difference(F4NegLongRoots, [
		[-1, -1, -1, 1], [1, 1, -1, 1], [1, -1, 1, 1], [-1, 1, 1, 1],
	]);
	minusSignRootsShort := [
		[1, 0, -1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [0, -1, -1, 0],
		[-1, 1, 0, 0], [-1, 0, 0, 1]
	];
	if root in Union(minusSignRootsLong, minusSignRootsShort) then
		a := -a;
	fi;
	G2Root := F4RootG2Coord(root);
	# L_{-2}
	if G2Root[1] = -2 then
		return a * LieX;
	# L_{-1}
	elif G2Root[1] = -1 then
		return BrownNegToLieEmb(BrownRootHomF4(root, a));
	# L_0
	elif G2Root = [0, 1] then
		return CubicPosToLieEmb(CubicRootHomF4(root, a, 1));
	elif G2Root = [0, -1] then
		return CubicNegToLieEmb(CubicRootHomF4(root, a, -1));
	elif G2Root = [0,0] then
		return DDToLieEmb(DDRootHomA2(root{[2..4]}, a));
	# L_1
	elif G2Root[1] = 1 then
		return BrownPosToLieEmb(BrownRootHomF4(root, a));
	# L_2
	elif G2Root[1] = 2 then
		return a * LieY;
	fi;
end);

# DeclareOperation("LiePartG2", [IsLieElement, IsList]);
# InstallMethod(LiePartG2, [IsLieElement, IsList])

# DeclareOperation("LiePartF4", [IsLieElement, IsList]);

# InstallMethod(LiePartF4, [IsLieElement, IsList], function(lieEl, root)

# end);

## ---- Generators ----

# comIndetNum, conicIndetNum: Numbers of the indeterminates that should be used.
# Output: A list of generic basic elements of Lie (as a Lie algebra), involving indeterminates
# t_comIndetNum, a_conicIndetNum
LieGensAsLie := function(comIndetNum, conicIndetNum)
	local a, t, gens, root;
	t := ComRingBasicIndet(comIndetNum);
	a := ConicAlgBasicIndet(conicIndetNum);
	gens := [LieX];
	for root in Filtered(F4Roots, x -> F4RootG2Coord(x)[1] = 1) do
		if root in F4ShortRoots then
			Add(gens, LieRootHomF4(root, a));
		else
			Add(gens, LieRootHomF4(root, t));
		fi;
	od;
	return gens;
end;

# comIndetNum, conicIndetNum: Numbers of the indeterminates that should be used.
# Output: A list of generic basic elements of Lie (as a module), involving indeterminates
# t_comIndetNum, a_conicIndetNum, a_{conicIndetNum+1}.
# Uses the formulas from [DMW, 5.20] (d_{a[ij],b[jk]} = TwistDiag[j]*d_{1[ii],ab[kk]})
# to reduce the number of generators.
LieGensAsModule := function(comIndetNum, conicIndetNum)
	local t1, a1, a2, gens, root, i, j, gen;
	t1 := ComRingBasicIndet(comIndetNum);
	a1 := ConicAlgBasicIndet(conicIndetNum);
	a2 := ConicAlgBasicIndet(conicIndetNum + 1);
	gens := [LieXi, LieZeta];
	# Generators outside DD
	for root in F4Roots do
		if F4RootG2Coord(root) <> [0, 0] then
			if root in F4ShortRoots then
				Add(gens, LieRootHomF4(root, a1));
			else
				Add(gens, LieRootHomF4(root, t1));
			fi;
		fi;
	od;
	# Generators in DD
	# Generators of Z_{i \to j} for i <> j and of Z_{ii,ii}
	for i in [1..3] do
		for j in [1..3] do
			if i = j then
				gen := Liedd(CubicComEl(i, One(ComRing)), CubicComEl(i, t1));
			else
				gen := Liedd(CubicComEl(i, One(ComRing)), CubicAlgElMat(i, j, a1));
			fi;
			Add(gens, gen);
		od;
	od;
	# Generators of Z_{ij,ji} for i <> j
	for i in [1..3] do
		for j in [i+1..3] do
			Add(gens, Liedd(CubicAlgElMat(i, j, a1), CubicAlgElMat(j, i, a2)));
		od;
	od;
	return gens;
end;

# (Probably not used)
# As LieGensAsModule, but does not use the formulas from [DMW, 5.20].
LieGensAsModuleUnsimplified := function(indetNum)
	local t1, a1, gens, root, cubic1, cubic2, cubicGens1, cubicGens2;
	t1 := ComRingBasicIndet(2*indetNum + 1);
	a1 := ConicAlgBasicIndet(2*indetNum + 1);
	gens := [LieXi, LieZeta];
	# Generators outside DD
	for root in F4Roots do
		if F4RootG2Coord(root) <> [0, 0] then
			if root in F4ShortRoots then
				Add(gens, LieRootHomF4(root, a1));
			else
				Add(gens, LieRootHomF4(root, t1));
			fi;
		fi;
	od;
	# Generators in DD
	cubicGens1 := CubicGensAsModule(2*indetNum + 1);
	cubicGens2 := CubicGensAsModule(2*indetNum + 2);
	for cubic1 in cubicGens1 do
		for cubic2 in cubicGens2 do
			Add(gens, Liedd(cubic1, cubic2));
		od;
	od;
	return gens;
end;
