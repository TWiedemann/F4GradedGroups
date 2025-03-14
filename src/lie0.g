SanitizeImmediately := true; # If true, DDSanitizeRep is applied after sever

# DD is the ComRing-span of all dd_{a,b} for a, b \in Cubic.
# An element c1 * dd_{a1, b1} + c2 * dd_{a2, b2} + ... is represented by
# the list [[c1, a1, b2], [c2, a2, b2], ...].

DDSanitizeRep := function(rep)
	local i, j, x;
	for i in [Length(rep), Length(rep)-1 .. 1] do
		if i > Length(rep) then
			# This may happen because we remove elements from rep during the loop
			continue;
		fi;
		x := rep[i];
		if x[1] = Zero(ComRing) then
			Remove(rep, i);
			continue;
		fi;
		for j in [1..i-1] do
			if rep[j][2] = x[2] and rep[j][3] = x[3] then
				rep[j][1] := rep[j][1] + x[1];
				Remove(rep, i);
				if rep[j][1] = Zero(ComRing) then
					Remove(rep, j);
				fi;
				break;
			fi;
		od;
	od;
end;

L0ZeroString := "0_{L_0}";
DDSymString := "\dd";

DDRepToString := function(a)
	local stringList, summand, s;
	stringList := [];
	for summand in a do
		s := Concatenation(DDSymString, "_{", String(summand[2]), ",", String(summand[3]), "}");
		if summand[1] <> One(ComRing) then
			s := Concatenation(String(summand[1]), "*", s); 
		fi;
		Add(stringList, s);
	od;
	return StringSum(stringList, L0ZeroString);
end;

DDSpec := rec(
	ElementName := "DDElement",
	Zero := a -> [],
	Addition := function(a, b)
		local sum;
		sum := Concatenation(a,b);
		if SanitizeImmediately then
			DDSanitizeRep(sum);
		fi;
		return sum;
	end,
	AdditiveInverse := function(a)
		local inv, i;
		inv := [];
		for i in [1..Length(a)] do
			Add(inv, [-a[i][1], a[i][2], a[i][3]]);
		od;
		return inv;
	end,
	Print := function(a)
		Print(DDRepToString(a));
	end,
	# Lie bracket on DD
	Multiplication := function(a, b)
		local productRep, summand1, summand2, x1, x2, y1, y2, z1, z2, coeff;
		# We do not sanitize the input because, under normal circumstances, it should already
		# be sanitized
		productRep := [];
		for summand1 in a do
			x1 := summand1[2];
			x2 := summand1[3];
			for summand2 in b do
				y1 := summand2[2];
				y2 := summand2[3];
				# summand1*summand2 = coeff * (dd_{D_{x1,x2}(y1), y2} - dd_{y1, D_{x2,x1}(y2)})
				# Here "D" is JordanD
				coeff := summand1[1] * summand2[1]; # in ComRing
				z1 := JordanD(x1, x2, y1);
				z2 := y2;
				if not IsZero(z1) then
					Add(productRep, [coeff, z1, z2]);
				fi;
				z1 := y1;
				z2 := JordanD(x2, x1, y2);
				if not IsZero(z2) then
					Add(productRep, [-coeff, z1, z2]);
				fi;
			od;
		od;
		if SanitizeImmediately then
			DDSanitizeRep(productRep);
		fi;
		return productRep;
	end
);

DD := ArithmeticElementCreator(DDSpec);
DDZero := DD([]);

# ddEl: c1*dd_{a1,b1} + c2*dd_{a2,b2} + ...
# Output: [[c1, a1, b1], [c2, a2, b2], ...]
DDCoeffList := function(ddEl)
	return UnderlyingElement(ddEl);
end;

InstallMethod(String, [IsDDElement], x -> DDRepToString(UnderlyingElement(x)));

DeclareOperation("dd", [IsCubicElement, IsCubicElement]);

InstallMethod(dd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	return DD([[One(ComRing), cubicEl1, cubicEl2]]);
end);

# rep: Internal representation of an element of L0
# Output: A string representing this element
L0RepToString := function(rep)
	local stringList, s, list, name, sym;
	stringList := [];
	for s in ["dd", "cubicPos", "cubicNeg"] do
		if not IsZero(rep.(s)) then
			Add(stringList, String(rep.(s)));
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
	return StringSum(stringList);
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
	Print := function()
		Print(L0RepToString);
	end,
	# Lie bracket
	Multiplication := function(a, b)
		local dd, xiCoeff, zetaCoeff, cubicPos, cubicNeg, summand, coeff, cubic1, cubic2;
		dd := a.dd*b.dd + 
			DD([[-One(ComRing), a.cubicPos, b.cubicNeg], [One(ComRing), b.cubicPos, a.cubicNeg]]);
		xiCoeff := Zero(ComRing);
		zetaCoeff := Zero(ComRing);
		cubicPos := a.zetaCoeff * b.cubicPos - b.zetaCoeff * a.cubicPos;
		cubicNeg := -a.zetaCoeff * b.cubicNeg + b.zetaCoeff * a.Neg;
		for summand in DDCoeffList(a.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos + JordanD(cubic1, cubic2, b.cubicPos);
			cubicNeg := cubicNeg - JordanD(cubic2, cubic1, b.cubicNeg);
		od;
		for summand in DDCoeffList(b.dd) do
			coeff := summand[1]; # in ComRing
			cubic1 := summand[2];
			cubic2 := summand[3];
			cubicPos := cubicPos - JordanD(cubic1, cubic2, a.cubicPos);
			cubicNeg := cubicNeg + JordanD(cubic2, cubic1, a.cubicNeg);
		od;
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

Xi := L0(rec(
	dd := DDZero,
	xiCoeff := One(ComRing),
	zetaCoeff := Zero(ComRing),
	cubicPos := CubicZero,
	cubicNeg := CubicZero
));

Zeta := L0(rec(
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
);
InstallMethod(L0ZetaCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).ZetaCoeff;
);
InstallMethod(L0CubicPosCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicPos;
);
InstallMethod(L0CubicNegCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).cubicNeg;
);
InstallMethod(L0DDCoeff, [IsL0Element], function(L0El)
	return UnderlyingElement(L0El).dd;
);

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
		return Brown(-BrownPart(a, 1), CubicZero, BrownPart(a, 3), 2*BrownPart(a, 4));
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
		return Brown(-2*BrownPart(a, 1), -BrownPart(a, 2), CubicZero, BrownPart(a, 4));
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
			## Components of brownEl
			lam := BrownPart(brownEl, 1);
			b := BrownPart(brownEl, 2);
			b2 := BrownPart(brownEl, 3);
			mu := BrownPart(brownEl, 4);
			## Return value
			# Action of Cubic and Cubic'
			newLam := -CubicTr(b, a2);
			newB := lam*a - CubicCross(a2, b2);
			newB2 := CubicCross(a, b) - mu*a2;
			newMu := CubicTr(a, b2);
			# Action of DD
			# ...
			result := Brown([newLam, newB, newB2, newMu]);
			if i = 1 then
				# Action of xi and zeta. This is the only part where i is relevant.
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