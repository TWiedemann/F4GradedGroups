### This file contains the definition of L0, the 0-part of the Lie algebra.

### Internal representation:
# Formally, L0 is the direct sum Cubic+(DD+ComRing*xi+ComRing*zeta)+Cubic'
# where the sum DD+ComRing*xi+ComRing*zeta need not be direct and where xi and zeta
# are formal elements. An element of L0 is represented as a record with entries
# "dd" (in DD), "xiCoeff" (in ComRing), "zetaCoeff" (in ComRing),
# "cubicPos" (in Cubic) and "cubicNeg" (in Cubic')

# ----- Definition and internal representation -----

_CubicInL0SymStringPos := "ad^+"; # c in Cubic is printed as ad^+_c
_CubicInL0SymStringNeg := "ad^-"; # c in Cubic' is printed as ad^-_c
_L0ZeroString := "0_{L_0}";

# rep: Internal representation of an element of L0
# Returns: A string representing this element
L0RepToString := function(rep)
	local stringList, s, list, name, sym;
	stringList := [];
	for s in ["dd", "cubicPos", "cubicNeg"] do
		if not IsZero(rep.(s)) then
			if s = "dd" then
				Add(stringList, String(rep.(s)));
			elif s = "cubicPos" then
				Add(stringList, Concatenation(_CubicInL0SymStringPos,
						"_{", String(rep.(s)), "}"));
			elif s = "cubicNeg" then
				Add(stringList, Concatenation(_CubicInL0SymStringNeg,
						"_{", String(rep.(s)), "}"));
			fi;
		fi;
	od;
	for list in [["xiCoeff", "\xi"], ["zetaCoeff", "\zeta"]] do
		name := list[1];
		sym := list[2];
		if rep.(name) <> Zero(ComRing) then
			if rep.(name) = One(ComRing) then
				Add(stringList, sym);
			else
				Add(stringList, Concatenation("(", String(rep.(name)), ")*", sym));
			fi;
		fi;
	od;
	return StringSum(stringList, "+", _L0ZeroString);
end;

L0Spec := rec(
	ElementName := "L0Element",
	Addition := function(a, b)
		return rec(
			dd := a.dd + b.dd,
			xiCoeff := a.xiCoeff + b.xiCoeff,
			zetaCoeff := a.zetaCoeff + b.zetaCoeff,
			cubicPos := a.cubicPos + b.cubicPos,
			cubicNeg := a.cubicNeg + b.cubicNeg
		);
	end,
	AdditiveInverse := function(a)
		return rec(
			dd := -a.dd,
			xiCoeff := -a.xiCoeff,
			zetaCoeff := -a.zetaCoeff,
			cubicPos := -a.cubicPos,
			cubicNeg := -a.cubicNeg
		);
	end,
	Zero := a -> rec(
		dd := DDZero,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := CubicZero
	),
	Print := function(a)
		Print(L0RepToString(a));
	end,
	# a, b: Representations of elements of L0
	# Returns: The Lie bracket of the corresponding elements
	Multiplication := function(a, b)
		local dd, xiCoeff, zetaCoeff, cubicPos, cubicNeg, summand, coeff, cubic1, cubic2;
		# Init components of [a,b]
		dd := DDZero;
		xiCoeff := Zero(ComRing);
		zetaCoeff := Zero(ComRing);
		cubicPos := CubicZero;
		cubicNeg := CubicZero;
		# [a.dd, b.dd] + [a.cubicPos, b.cubicNeg] + [a.cubicNeg, b.cubicPos]
		# ([ad_{a'}, ad_a] = dd(a, a'))
		dd := a.dd*b.dd + 
			DD([[-One(ComRing), a.cubicPos, b.cubicNeg], [One(ComRing), b.cubicPos, a.cubicNeg]]);
		# [a.zeta, b.cubicPos + b.cubicNeg] + [a.cubicPos + a.cubicNeg, b.zeta]
		# ([zeta, ad_a] = ad_a and [zeta, ad_{a'}] = -ad_{a'})
		cubicPos := a.zetaCoeff * b.cubicPos - b.zetaCoeff * a.cubicPos;
		cubicNeg := -a.zetaCoeff * b.cubicNeg + b.zetaCoeff * a.cubicNeg;
		# [a.dd, b.cubicPos + b.cubicNeg]
		for summand in DDCoeffList(a.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos + coeff*JordanD(cubic1, cubic2, b.cubicPos);
			cubicNeg := cubicNeg - coeff*JordanD(cubic2, cubic1, b.cubicNeg);
		od;
		# [a.cubicPos + b.cubicNeg, b.dd]
		for summand in DDCoeffList(b.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos - coeff*JordanD(cubic1, cubic2, a.cubicPos);
			cubicNeg := cubicNeg + coeff*JordanD(cubic2, cubic1, a.cubicNeg);
		od;
		# Every other pair of summands has zero bracket: xi and zeta centralise DD+xi+zeta
		# and xi centralises L0.
		return rec(
			dd := dd,
			xiCoeff := xiCoeff,
			zetaCoeff := zetaCoeff,
			cubicPos := cubicPos,
			cubicNeg := cubicNeg
		);
	end
);

L0 := ArithmeticElementCreator(L0Spec);

InstallMethod(String, [IsL0Element], x -> L0RepToString(UnderlyingElement(x)));

# ----- Constructors for elements of L0 -----

L0Zero := L0(L0Spec.Zero(fail));

L0Xi := L0(rec(
	dd := DDZero,
	xiCoeff := One(ComRing),
	zetaCoeff := Zero(ComRing),
	cubicPos := CubicZero,
	cubicNeg := CubicZero
));

L0Zeta := L0(rec(
	dd := DDZero,
	xiCoeff := Zero(ComRing),
	zetaCoeff := One(ComRing),
	cubicPos := CubicZero,
	cubicNeg := CubicZero
));

DeclareOperation("CubicPosToL0Emb", [IsCubicElement]);
DeclareOperation("CubicNegToL0Emb", [IsCubicElement]);
DeclareOperation("DDToL0Emb", [IsDDElement]);

# a: Element of Cubic.
# Returns: ad_a^+ \in L0.
InstallMethod(CubicPosToL0Emb, [IsCubicElement], function(a)
	return L0(rec(
		dd := DDZero,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := a,
		cubicNeg := CubicZero
	));
end);

# a: Element of Cubic.
# Returns: ad_a^- \in L0.
InstallMethod(CubicNegToL0Emb, [IsCubicElement], function(a)
	return L0(rec(
		dd := DDZero,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := a
	));
end);

# ddEl: Element of DD.
# Returns: The corresponding element of L0.
InstallMethod(DDToL0Emb, [IsDDElement], function(ddEl)
	return L0(rec(
		dd := ddEl,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := CubicZero
	));
end);

# cubicEl1, cubicEl2: Elements of Cubic.
# Returns: dd_{cubicEl1, cubicEl2} \in L0.
DeclareOperation("L0dd", [IsCubicElement, IsCubicElement]);
InstallMethod(L0dd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	return DDToL0Emb(DDdd(cubicEl1, cubicEl2));
end);

# ---- Getter functions for parts of elements of L0 ----

DeclareOperation("L0XiPart", [IsL0Element]);
DeclareOperation("L0ZetaPart", [IsL0Element]);
DeclareOperation("L0CubicPosPart", [IsL0Element]);
DeclareOperation("L0CubicNegPart", [IsL0Element]);
DeclareOperation("L0DDPart", [IsL0Element]);

InstallMethod(L0XiPart, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).xiCoeff;
end);
InstallMethod(L0ZetaPart, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).zetaCoeff;
end);
InstallMethod(L0CubicPosPart, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicPos;
end);
InstallMethod(L0CubicNegPart, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicNeg;
end);
InstallMethod(L0DDPart, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).dd;
end);

InstallOtherMethod(IsZero, [IsL0Element], function(L0el)
	return IsZero(L0XiPart(L0el)) and IsZero(L0ZetaPart(L0el)) and IsZero(L0DDPart(L0el))
		and IsZero(L0CubicPosPart(L0el)) and IsZero(L0CubicNegPart(L0el));
end);

# ----- Scalar multiplication ComRing x L0 -> L0 -----
InstallOtherMethod(\*, "for ComRingElement and L0Element", [IsRingElement, IsL0Element], 2, function(comEl, L0El)
	return L0(rec(
		dd := comEl * L0DDPart(L0El),
		xiCoeff := comEl * L0XiPart(L0El),
		zetaCoeff := comEl * L0ZetaPart(L0El),
		cubicPos := comEl * L0CubicPosPart(L0El),
		cubicNeg := comEl * L0CubicNegPart(L0El)
	));
end);

# ----- Action of L0 on Lie -----

# a: Element of ComRing or of Brown
# Returns: The result of the action of xi on...
# - ...a*LieY (\in L_2) if a in Comring
# - ...a_+ if a in Brown
XiEndo := function(a, sign)
	if a in ComRing then
		return sign*2*a;
	elif IsBrownElement(a) then
		return sign*a;
	else
		Error("xi not defined on this element");
		return fail;
	fi;
end;

# a: Element of ComRing or of Brown
# Returns: The result of the action of zeta on...
# - ...a*LieY (\in L_2) if a in Comring
# - ...a_+ if a in Brown
ZetaEndo := function(a, sign)
	if not sign in [1, -1] then
		Error("Argument must be a sign");
		return fail;
	fi;
	if a in ComRing then
		return sign*a;
	elif IsBrownElement(a) then
		if sign = 1 then
			return Brown([-BrownElPart(a, 1), CubicZero, BrownElPart(a, 3), 2*BrownElPart(a, 4)]);
		else
			return Brown([-2*BrownElPart(a, 1), -BrownElPart(a, 2), CubicZero, BrownElPart(a, 4)]);
		fi;
	else
		Error("zeta not defined on this element");
		return fail;
	fi;
end;

# L0El: Element of L0.
# i: -2, -1, 1, or 2.
# Returns: The function L_i -> L_i, a -> L0El*a. Here L_{-2} and L_2 are identified with ComRing.
DeclareOperation("L0ElAsEndo", [IsL0Element, IsInt]);
InstallMethod(L0ElAsEndo, [IsL0Element, IsInt], function(L0El, i)
	local xi, zeta, a, a2, ddList;
	# Components of L0El
	xi := L0XiPart(L0El);
	zeta := L0ZetaPart(L0El);
	a := L0CubicPosPart(L0El);
	a2 := L0CubicNegPart(L0El);
	ddList := DDCoeffList(L0DDPart(L0El));
	if i = -2 then
		return function(comEl)
			# Cubic, Cubic' and DD act trivially
			ReqComRingEl(comEl);
			return -(2*L0XiPart(L0El) + L0ZetaPart(L0El)) * comEl;
		end;
	elif i = 1 or i = -1 then # The actions on L_1 and on L_{-1} are nearly identical
		return function(brownEl)
			local lam, b, b2, mu, newLam, newB, newB2, newMu, coeff, c, c2, result, summand;
			## Components of brownEl
			lam := BrownElPart(brownEl, 1);
			b := BrownElPart(brownEl, 2);
			b2 := BrownElPart(brownEl, 3);
			mu := BrownElPart(brownEl, 4);
			## Return value
			# Action of Cubic and Cubic'
			newLam := -CubicBiTr(b, a2);
			newB := lam*a - CubicCross(a2, b2);
			newB2 := CubicCross(a, b) - mu*a2;
			newMu := CubicBiTr(a, b2);
			# Action of DD
			for summand in ddList do
				coeff := summand[1]; # in ComRing
				c := summand[2]; # in Cubic
				c2 := summand[3]; # in Cubic'
				newLam := newLam - coeff*lam*CubicBiTr(c, c2);
				newB := newB + coeff*(JordanD(c, c2, b) - CubicBiTr(c, c2)*b);
				newB2 := newB2 + coeff*(-JordanD(c2, c, b2) + CubicBiTr(c, c2)*b2);
				newMu := newMu + coeff*(mu*CubicBiTr(c, c2));
			od;
			result := BrownElFromTuple(newLam, newB, newB2, newMu);
			# Action of xi and zeta. This is the only part where i is relevant.
			result := result + xi*XiEndo(brownEl, i) + zeta*ZetaEndo(brownEl, i);
			return result;
		end;
	elif i = 2 then
		return function(comEl)
			# Cubic, Cubic' and DD act trivially
			ReqComRingEl(comEl);
			return (2*L0XiPart(L0El) + L0ZetaPart(L0El)) * comEl;
		end;
	else
		return fail;
	fi;
end);
