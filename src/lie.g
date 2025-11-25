### This file contains the definition of the Lie algebra which we refer to as Lie
### (or sometimes as L).

### Internal representation:
# Lie is the direct sum ComRing*LieX + Brown_- + L0 + Brown_+ + ComRing*LieY
# where LieX, LieY are formal elements.
# Elements are represented as records with entries
# "neg2" (in ComRing), "neg1" (in Brown), "zero" (in L0), "pos1" (in Brown), "pos2" (in ComRing).

# ----- Display of elements -----

_LieZeroString := "0_L";
_LieNeg2String := "x";
_LiePos2String := "y";

# rep: Internal representation of an element of L.
# Returns: A string representing this element.
LieRepToString := function(rep)
	local stringList, name, s;
	stringList := [];
	for name in ["neg2", "neg1", "zero", "pos1", "pos2"] do
		if not IsZero(rep.(name)) then
			s := String(rep.(name));
			if name = "neg2" then
				s := Concatenation("(", s, ")*", _LieNeg2String);
			elif name = "pos2" then
				s := Concatenation("(", s, ")*", _LiePos2String);
			elif name = "pos1" then
				s := Concatenation(s, "_+");
			elif name = "neg1" then
				s := Concatenation(s, "_-");
			fi;
			Add(stringList, s);
		fi;
	od;
	return StringSum(stringList, " + ", _LieZeroString); # Extra space around "+"
end;

# ----- Helper functions for the Lie bracket -----

DeclareOperation("_LieBracketBrownPosPos", [IsBrownElement, IsBrownElement]);
DeclareOperation("_LieBracketBrownNegPos", [IsBrownElement, IsBrownElement]);

# brown1, brown2: Element of Brown, regarded as element of L_1.
# Returns: t in ComRing such that [brown1, brown2] = t * LieY.
# If brown1, brown2 are regarded as elements of L_{-1}, the output t satisfies
# that [brown1, brown2] = t * LieX.
InstallMethod(_LieBracketBrownPosPos, [IsBrownElement, IsBrownElement], function(brown1, brown2)
	local lam, b1, b2, mu, nu, c1, c2, rho;
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
# Returns: [brown1, brown2] (\in L0)
InstallMethod(_LieBracketBrownNegPos, [IsBrownElement, IsBrownElement], function(brown1, brown2)
	local lam, b1, b2, mu, nu, c1, c2, rho;
	lam := BrownElPart(brown1, 1);
	b1 := BrownElPart(brown1, 2);
	b2 := BrownElPart(brown1, 3);
	mu := BrownElPart(brown1, 4);
	nu := BrownElPart(brown2, 1);
	c1 := BrownElPart(brown2, 2);
	c2 := BrownElPart(brown2, 3);
	rho := BrownElPart(brown2, 4);
	return Sum([
		CubicNegToL0Emb(-lam*c2 + CubicCross(b1, c1) - nu*b2),
		(lam*rho - CubicBiTr(b1, c2)) * L0Zeta,
		(CubicBiTr(c1, b2) - mu*nu) * (L0Xi - L0Zeta),
		L0dd(b1, c2) + L0dd(c1, b2),
		CubicPosToL0Emb(-rho*b1 + CubicCross(b2, c2) - mu*c1)
	]);
end);

# ----- Definition of Lie -----

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
		neg2 := neg2 - L0ElAsEndo(b.zero, -2)(a.neg2); # [a.neg2, b.zero]
		neg1 := neg1 - a.neg2*b.pos1; # [a.neg2, b.pos1];
		zero := zero + a.neg2*b.pos2*L0Xi; # [a.neg2, b.pos2]
		# [a.neg1, b]
		neg2 := neg2 + _LieBracketBrownPosPos(a.neg1, b.neg1); # [a.neg1, b.neg1]
		neg1 := neg1 - L0ElAsEndo(b.zero, -1)(a.neg1); # [a.neg1, b.zero]
		zero := zero + _LieBracketBrownNegPos(a.neg1, b.pos1); # [a.neg1, b.pos1]
		pos1 := pos1 - b.pos2 * a.neg1; # [a.neg1, b.pos2]
		# [a.zero, b]
		neg2 := neg2 + L0ElAsEndo(a.zero, -2)(b.neg2); # [a.zero, b.neg2]
		neg1 := neg1 + L0ElAsEndo(a.zero, -1)(b.neg1); # [a.zero, b.neg1]
		zero := zero + a.zero*b.zero; # [a.zero, b.zero]
		pos1 := pos1 + L0ElAsEndo(a.zero, 1)(b.pos1); # [a.zero, b.pos1]
		pos2 := pos2 + L0ElAsEndo(a.zero, 2)(b.pos2); # [a.zero, b.pos2]
		# [a.pos1, b]
		neg1 := neg1 + b.neg2 * a.pos1; # [a.pos1, b.neg2]
		zero := zero - _LieBracketBrownNegPos(b.neg1, a.pos1); # [a.pos1, b.neg1]
		pos1 := pos1 - L0ElAsEndo(b.zero, 1)(a.pos1); # [a.pos1, b.zero]
		pos2 := pos2 + _LieBracketBrownPosPos(a.pos1, b.pos1); # [a.pos1, b.pos1]
		# [a.pos2, b]
		zero := zero - a.pos2*b.neg2*L0Xi; # [a.pos2, b.neg2]
		pos1 := pos1 + a.pos2*b.neg1; # [a.pos2, b.neg1]
		pos2 := pos2 - L0ElAsEndo(b.zero, 2)(a.pos2); # [a.pos2, b.zero]
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

# ----- Constructors and embeddings for elements of Lie -----

LieZero := Lie(LieSpec.Zero(fail));

DeclareOperation(
	"LieElFromTuple",
	[IsRingElement, IsBrownElement, IsL0Element, IsBrownElement, IsRingElement]
);
InstallMethod(
	LieElFromTuple,
	[IsRingElement, IsBrownElement, IsL0Element, IsBrownElement, IsRingElement],
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
DeclareOperation(
	"LieBrownPosElFromTuple",
	[IsRingElement, IsCubicElement, IsCubicElement, IsRingElement]
);
DeclareOperation(
	"LieBrownNegElFromTuple",
	[IsRingElement, IsCubicElement, IsCubicElement, IsRingElement]
);
DeclareOperation("CubicPosToLieEmb", [IsCubicElement]);
DeclareOperation("CubicNegToLieEmb", [IsCubicElement]);

# L0 -> Lie_0
InstallMethod(L0ToLieEmb, [IsL0Element], function(L0el)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0el, BrownZero, Zero(ComRing));
end);

# DD -> Lie_0
InstallMethod(DDToLieEmb, [IsDDElement], x -> L0ToLieEmb(DDToL0Emb(x)));

# Brown -> Lie_1
InstallMethod(BrownPosToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), BrownZero, L0Zero, brownEl, Zero(ComRing));
end);

# Brown -> Lie_{-1}
InstallMethod(BrownNegToLieEmb, [IsBrownElement], function(brownEl)
	return LieElFromTuple(Zero(ComRing), brownEl, L0Zero, BrownZero, Zero(ComRing));
end);

# [ComRing, Cubic, Cubic', ComRing] -> Lie_1
InstallMethod(
	LieBrownPosElFromTuple,
	[IsRingElement, IsCubicElement, IsCubicElement, IsRingElement], 
	function(a, b, c, d)
		return BrownPosToLieEmb(BrownElFromTuple(a, b, c, d));
	end
);

# [ComRing, Cubic, Cubic', ComRing] -> Lie_{-1}
InstallMethod(
	LieBrownNegElFromTuple,
	[IsRingElement, IsCubicElement, IsCubicElement, IsRingElement], 
	function(a, b, c, d)
		return BrownNegToLieEmb(BrownElFromTuple(a, b, c, d));
	end
);

# Cubic -> Lie_{0,-1}
InstallMethod(CubicPosToLieEmb, [IsCubicElement], function(cubicEl)
	return L0ToLieEmb(CubicPosToL0Emb(cubicEl));
end);

# Cubic -> Lie_{0,1}
InstallMethod(CubicNegToLieEmb, [IsCubicElement], function(cubicEl)
	return L0ToLieEmb(CubicNegToL0Emb(cubicEl));
end);

# cubicEl1, cubicEl2: Elements of Cubic.
# Returns: dd_{cubicEl1, cubicEl2} \in Lie.
DeclareOperation("Liedd", [IsCubicElement, IsCubicElement]);
InstallMethod(Liedd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	return L0ToLieEmb(L0dd(cubicEl1, cubicEl2));
end);

LieZeta := L0ToLieEmb(L0Zeta);
LieXi := L0ToLieEmb(L0Xi);

# comRingIndetNum, conicAlgIndetNum: Integers.
# Returns: A list of "generic generators" of L_0000 using the indeterminates
# t_{comIndetNum}, a_{conicIndetNum}, a_{conicIndetNum+1}.
Lie0000Gens := function(comIndetNum, conicIndetNum)
	local t1, a1, a2, result, i, j;
	t1 := ComRingIndet(comIndetNum);
	a1 := ConicAlgIndet(conicIndetNum);
	a2 := ConicAlgIndet(conicIndetNum+1);
	result := [t1*LieXi, t1*LieZeta];
	for i in [1,2,3] do
		Add(result, Liedd(CubicComEl(i, One(ComRing)), CubicComEl(i, t1)));
		for j in [i+1..3] do
			Add(result, Liedd(CubicAlgElMat(i, j, a1), CubicAlgElMat(j, i, a2)));
		od;
	od;
	return result;
end;

# ----- Getter functions for components of elements of Lie -----

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

# lieEl: Element of Lie.
# Returns: true if lieEl "obviously" lies in
# L_0000 = \sum_i DD_{i \to i} + ComRing*LieXi + ComRing*LieZeta,
# and otherwise false. Here "obviously" means that we only check that all coefficients
# of the parts outside of L_0000 are internally represented by 0. Hence this function should
# should only be called on elements that have been simplified beforehand, and may of course
# return false negatives. However, it does not return false positives.
DeclareOperation("IsInLie0000", [IsLieElement]);
InstallMethod(IsInLie0000, [IsLieElement], function(lieEl)
	local i, lie0, coeff, a, b, c, sumA, sumB, func, int;
	# Check positive and negative parts L_i
	for i in [-2, -1, 1, 2] do
		if not IsZero(LiePart(lieEl, i)) then
			return false;
		fi;
	od;
	lie0 := LiePart(lieEl, 0);
	# Check L_{01} and L_{0,-1}
	for func in [L0CubicPosCoeff, L0CubicNegCoeff] do
		if not IsZero(func(lie0)) then
			return false;
		fi;
	od;
	# Check L_00
	for coeff in DDCoeffList(L0DDCoeff(lie0)) do
		# coeff = c*dd_{a,b} represented as [c, a, b]
		c := coeff[1]; # \in ComRing
		a := coeff[2]; # \in Cubic
		b := coeff[3]; # \in Cubic'
		if not IsZero(c) then
			for sumA in Summands(a) do
				for sumB in Summands(b) do
					# summand = x[ij] is represented as [i, j, x]
					if not IsZero(sumA[3]) and not IsZero(sumB[3]) then
						int := Intersection([sumA[1], sumA[2]], [sumB[1], sumB[2]]);
						if Size(int) = 0 then # dd_{a,b} = 0 by Peirce law
							continue;
						elif Size(int) = 2 then
							continue; # dd_{a,b} in DD_{i \to i} for i = sumA[1]
						else
							if Size(Set([sumA[1], sumA[2], sumB[1], sumB[2]])) = 1 then
								continue; # dd_{a,b} in DD_{i \to i} for i = sumA[1]
							else
								return false;
							fi;
						fi;
					fi;
				od;
			od;
		fi;
	od;
	return true;
end);

# ----- Further operations -----

# Scalar multiplication ComRing x Lie -> Lie
InstallOtherMethod(\*, "for ComRingElement and LieElement", [IsRingElement, IsLieElement], 2, function(comEl, lieEl)
	return Lie(rec(
		neg2 := comEl * LiePart(lieEl, -2),
		neg1 := comEl * LiePart(lieEl, -1),
		zero := comEl * LiePart(lieEl, 0),
		pos1 := comEl * LiePart(lieEl, 1),
		pos2 := comEl * LiePart(lieEl, 2)
	));
end);

# ----- Display and String for elements of Lie -----

InstallMethod(String, [IsLieElement], x -> LieRepToString(UnderlyingElement(x)));

# The zero element is displayed as O_L. For every other element, we display the
# 5 parts of lieEl separately, except for the parts which are zero.
InstallMethod(Display, [IsLieElement], function(lieEl)
	local i, part;
	if IsZero(lieEl) then
		Print(String(lieEl), "\n");
	else
		for i in [-2..2] do
			part := LiePart(lieEl, i);
			if not IsZero(part) then
				if i >= 0 then
					Print(" ");
				fi;
				Print(String(i), " part: ", String(part), "\n");
			fi;
		od;
	fi;
end);
