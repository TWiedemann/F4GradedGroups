CubicInL0SymStringPos := "ad^+"; # c in Cubic is printed as ad^+_c
CubicInL0SymStringNeg := "ad^-"; # c in Cubic' is printed as ad^-_c

# rep: Internal representation of an element of L0
# Output: A string representing this element
L0RepToString := function(rep)
	local stringList, s, list, name, sym;
	stringList := [];
	for s in ["dd", "cubicPos", "cubicNeg"] do
		if not IsZero(rep.(s)) then
			if s = "dd" then
				Add(stringList, String(rep.(s)));
			elif s = "cubicPos" then
				Add(stringList, Concatenation(CubicInL0SymStringPos,
						"_{", String(rep.(s)), "}"));
			elif s = "cubicPos" then
				Add(stringList, Concatenation(CubicInL0SymStringNeg,
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
				Add(stringList, Concatenation("(", String(rep.(name)), ")", sym));
			fi;
		fi;
	od;
	return StringSum(stringList, L0ZeroString);
end;

# Elements of L0 are represented by records with entries "dd", "xiCoeff", "zetaCoeff",
# "cubicPos" and "cubicNeg"
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
		dd := [],
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := CubicZero
	),
	Print := function(a)
		Print(L0RepToString(a));
	end,
	# Lie bracket
	Multiplication := function(a, b)
		local dd, xiCoeff, zetaCoeff, cubicPos, cubicNeg, summand, coeff, cubic1, cubic2;
		# Init components of [a,b]
		dd := DDZero;
		xiCoeff := Zero(ComRing);
		zetaCoeff := Zero(ComRing);
		cubicPos := CubicZero;
		cubicNeg := CubicZero;
		# [a.dd, b.dd] + [a.cubicPos, b.cubicNeg] + [a.cubicNeg, b.cubicPos]
		# ([ad_{a'}, ad_a] = dd(a, a') by [DMW, 3.5])
		dd := a.dd*b.dd + 
			DD([[-One(ComRing), a.cubicPos, b.cubicNeg], [One(ComRing), b.cubicPos, a.cubicNeg]]);
		# [a.zeta, b.cubicPos + b.cubicNeg] + [a.cubicPos + a.cubicNeg, b.zeta]
		# ([zeta, ad_a] = ad_a and [zeta, ad_{a'}] = -ad_{a'} by [DMW, 3.7])
		cubicPos := a.zetaCoeff * b.cubicPos - b.zetaCoeff * a.cubicPos;
		cubicNeg := -a.zetaCoeff * b.cubicNeg + b.zetaCoeff * a.cubicNeg;
		# [a.dd, b.cubicPos + b.cubicNeg]
		for summand in DDCoeffList(a.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos + JordanD(cubic1, cubic2, b.cubicPos);
			cubicNeg := cubicNeg - JordanD(cubic2, cubic1, b.cubicNeg);
		od;
		# [a.cubicPos + b.cubicNeg, b.dd]
		for summand in DDCoeffList(b.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos - JordanD(cubic1, cubic2, a.cubicPos);
			cubicNeg := cubicNeg + JordanD(cubic2, cubic1, a.cubicNeg);
		od;
		# Every other pair of summands has zero bracket: xi and zeta centralise DD+xi+zeta
		# and xi centralises L0 ([DMW, 3.7]).
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
L0Zero := L0(L0Spec.Zero(fail));

InstallMethod(String, [IsL0Element], x -> L0RepToString(UnderlyingElement(x)));

## Constructors for elements of L0

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

InstallMethod(CubicPosToL0Emb, [IsCubicElement], function(a)
	return L0(rec(
		dd := DDZero,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := a,
		cubicNeg := CubicZero
	));
end);

InstallMethod(CubicNegToL0Emb, [IsCubicElement], function(a)
	return L0(rec(
		dd := DDZero,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := a
	));
end);

InstallMethod(DDToL0Emb, [IsDDElement], function(ddEl)
	return L0(rec(
		dd := ddEl,
		xiCoeff := Zero(ComRing),
		zetaCoeff := Zero(ComRing),
		cubicPos := CubicZero,
		cubicNeg := CubicZero
	));
end);

DeclareOperation("ddL0", [IsCubicElement, IsCubicElement]);
InstallMethod(ddL0, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	return DDToL0Emb(dd(cubicEl1, cubicEl2));
end);

## Getters for parts of elements of L0

DeclareOperation("L0XiCoeff", [IsL0Element]);
DeclareOperation("L0ZetaCoeff", [IsL0Element]);
DeclareOperation("L0CubicPosCoeff", [IsL0Element]);
DeclareOperation("L0CubicNegCoeff", [IsL0Element]);
DeclareOperation("L0DDCoeff", [IsL0Element]);

InstallMethod(L0XiCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).xiCoeff;
end);
InstallMethod(L0ZetaCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).zetaCoeff;
end);
InstallMethod(L0CubicPosCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicPos;
end);
InstallMethod(L0CubicNegCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicNeg;
end);
InstallMethod(L0DDCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).dd;
end);

## Scalar multiplication ComRing x L0 -> L0
InstallOtherMethod(\*, "for ComRingElement and L0Element", [IsRingElement, IsL0Element], 2, function(comEl, L0El)
	return L0(rec(
		dd := comEl * L0DDCoeff(L0El),
		xiCoeff := comEl * L0XiCoeff(L0El),
		zetaCoeff := comEl * L0ZetaCoeff(L0El),
		cubicPos := comEl * L0CubicPosCoeff(L0El),
		cubicNeg := comEl * L0CubicNegCoeff(L0El)
	));
end);

## Action of L0 on Lie

# a: Element of ComRing or of Brown
# Output: The result of the action of xi on a (regarded as an element of L_1 or L_2)
XiPosEndo := function(a)
	if a in ComRing then
		return 2*a;
	elif IsBrownElement(a) then
		return a;
	else
		Error("xi not defined on this element");
		return fail;
	fi;
end;

# a: Element of ComRing or of Brown
# Output: The result of the action of xi on a (regarded as an element of L_{-1} or L_{-2})
XiNegEndo := function(a)
	if a in ComRing then
		return -2*a;
	elif IsBrownElement(a) then
		return -a;
	else
		Error("xi not defined on this element");
		return fail;
	fi;
end;

# a: Element of ComRing or of Brown
# Output: The result of the action of zeta on a (regarded as an element of L_1 or L_2)
ZetaPosEndo := function(a)
	if a in ComRing then
		return a;
	elif IsBrownElement(a) then
		return Brown([-BrownElPart(a, 1), CubicZero, BrownElPart(a, 3), 2*BrownElPart(a, 4)]);
	else
		Error("zeta not defined on this element");
		return fail;
	fi;
end;

# a: Element of ComRing or of Brown
# Output: The result of the action of zeta on a (regarded as an element of L_{-1} or L_{-2})
ZetaNegEndo := function(a)
	if a in ComRing then
		return -a;
	elif IsBrownElement(a) then
		return Brown([-2*BrownElPart(a, 1), -BrownElPart(a, 2), CubicZero, BrownElPart(a, 4)]);
	else
		Error("zeta not defined on this element");
		return fail;
	fi;
end;

DeclareOperation("L0AsEndo", [IsL0Element, IsInt]);
InstallMethod(L0AsEndo, [IsL0Element, IsInt], function(L0El, i)
	local xi, zeta, a, a2, ddList;
	# Components of L0El
	xi := L0XiCoeff(L0El);
	zeta := L0ZetaCoeff(L0El);
	a := L0CubicPosCoeff(L0El);
	a2 := L0CubicNegCoeff(L0El);
	ddList := DDCoeffList(L0DDCoeff(L0El));
	if i = -2 then
		return function(comEl)
			# Cubic, Cubic' and DD act trivially
			if not comEl in ComRing then
				Error("Invalid input for L0 acting on L_{-2}");
			fi;
			return -(2*L0XiCoeff(L0El) + L0ZetaCoeff(L0El)) * comEl;
		end;
	elif i = 1 or i = -1 then
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
				newLam := newLam - lam*CubicBiTr(c, c2);
				newB := newB + JordanD(c, c2, b) - CubicBiTr(c, c2)*b;
				newB2 := newB2 - JordanD(c2, c, b2) + CubicBiTr(c, c2)*b2;
				newMu := newMu + mu*CubicBiTr(c, c2);
			od;
			result := Brown([newLam, newB, newB2, newMu]);
			# Action of xi and zeta. This is the only part where i is relevant.
			if i = 1 then
				result := result + xi*XiPosEndo(brownEl) + zeta*ZetaPosEndo(brownEl);
			else
				result := result + xi*XiNegEndo(brownEl) + zeta*ZetaNegEndo(brownEl);
			fi;
			return result;
		end;
	elif i = 2 then
		return function(comEl)
			# Cubic, Cubic' and DD act trivially
			if not comEl in ComRing then
				Error("Invalid input for L0 acting on L_2");
			fi;
			return (2*L0XiCoeff(L0El) + L0ZetaCoeff(L0El)) * comEl;
		end;
	else
		return fail;
	fi;
end);