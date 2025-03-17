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
	return StringSum(stringList, LieZeroString);
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

DeclareOperation("L0ToLieEmb", [IsL0Element]);
DeclareOperation("BrownPosToLieEmb", [IsBrownElement]);
DeclareOperation("BrownNegToLieEmb", [IsBrownElement]);

InstallMethod(L0ToLieEmb, [IsL0Element], function(L0el)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0el, BrownZero, Zero(ComRing));
end);

InstallMethod(BrownPosToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0Zero, brownEl, Zero(ComRing));
end);

InstallMethod(BrownNegToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), brownEl, L0Zero, BrownZero, Zero(ComRing));
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

# Display and String

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