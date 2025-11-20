### This file contains the definition of the root homomorphisms into the automorphism group
### of Lie. It is contained in the space LieEndo of module endomorphisms of Lie, which
### we refer to as LieEndo.

### Internal representation
# Elements of LieEndo are represented by GAP functions from Lie to Lie

# ----- Definition of LieEndo -----

LieEndoSpec := rec(
	ElementName := "LieEndo",
	# Zero map
	Zero := a -> function(x)
		if not IsLieElement(x) then
			Error("Function only defined on elements of Lie");
			return fail;
		else
			return LieZero;
		fi;
	end,
	# Identity map
	One := a -> function(x)
		if not IsLieElement(x) then
			Error("Function only defined on elements of Lie");
			return fail;
		else
			return x;
		fi;
	end,
	Print := function(a)
		Print("Endomorphism of the Lie algebra");
	end,
	Addition := function(f, g)
		return x -> f(x) + g(x);
	end,
	AdditiveInverse := function(f)
		return x -> -f(x);
	end,
	Multiplication := function(f, g)
		return x -> f(g(x));
	end,
	MathInfo := IsAdditivelyCommutativeElement
);

LieEndo := ArithmeticElementCreator(LieEndoSpec);
GrpOne := LieEndo(LieEndoSpec.One(fail));
GrpZero := LieEndo(LieEndoSpec.Zero(fail));

# For f \in LieEndo and a \in Lie, we want to write f(a) for the image of a under f.
InstallMethod(CallFuncList,
    "Allow function-like syntax for LieEndo",
    [IsLieEndo, IsList],
    function(f, args)
        if Length(args) = 1 and IsLieElement(args[1]) then
            return UnderlyingElement(f)(args[1]);
        else
            Error("Invalid argument type for LieEndo application");
        fi;
    end
);

# ----- General exponential maps (assuming that certain integers are invertible) -----

# These functions are only used to test that the root homomorphisms defined by
# explicit formulas coincide with the one given by exponentiation if 2 and 3 are
# invertible.

DeclareOperation("F4Exp", [IsLieElement]);
DeclareOperation("F4Exp", [IsLieElement, IsInt]);

# a: Element of Lie
# n: Integer, n > 0
# Returns: \sum_{i=0}^n (1/i!) * ad_a^i (as an element of LieEndo)
InstallMethod(F4Exp, [IsLieElement, IsInt], function(a, n)
	return LieEndo(function(x)
		local lastSummand, result, i;
		if not IsLieElement(x) then
			Error("Function only defined on elements of Lie");
			return fail;
		fi;
		lastSummand := x;
		result := x;
		for i in [1..n] do
			lastSummand := ((1/i)*One(ComRing)) * (a * lastSummand);
			result := result + lastSummand;
		od;
		return result;
	end);
end);

# For elements a of F4-root spaces, we know that ad_a^4 = 0.
InstallMethod(F4Exp, [IsLieElement], a -> F4Exp(a, 3));

## ----- Root homomorphisms in LieEndo -----

# Explicit formulas for all roots except for those in the (0, 0)-part
DeclareOperation("GrpRootHomF4NonDiv", [IsList, IsRingElement, IsBool]);
DeclareOperation("GrpRootHomF4NonDiv", [IsList, IsRingElement]);

# root: Root in F4.
# a: Element of ComRing if root is long and element of ConicAlg otherwise
# naive: Bool.
# Returns: The exponential of LieRootHomF4(root, a, naive, naive), defined by explicit
# formulas without divisions by 2 and 3.
InstallMethod(GrpRootHomF4NonDiv, [IsList, IsRingElement, IsBool], function(root, a, naive)
	local rootG2, lieXCoeff, lieNeg1, lie0, lieDDCoeffList, lieXiCoeff, lieZetaCoeff,
		liePos1, lieYCoeff, result, rho, b, bBrown, bLie, b2, c, c2, nu, scalar,
		list, lieCubicNeg, lieCubicPos, aLie, aBrown, lam, mu, nextSummand,
		aCubic, aCubic2, sign, brown, LieBrownElFromTuple, liehom;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
	liehom := function(root2, a2)
		return LieRootHomF4(root2, a2, naive, naive);
	end;
	rootG2 := F4RootG2Coord(root);
	return LieEndo(function(lieEl)
		# Components of lieEl
		lieXCoeff := LiePart(lieEl, -2);
		lieNeg1 := LiePart(lieEl, -1);
		lie0 := LiePart(lieEl, 0);
		lieDDCoeffList := DDCoeffList(L0DDCoeff(lie0));
		lieXiCoeff := L0XiCoeff(lie0);
		lieZetaCoeff := L0ZetaCoeff(lie0);
		lieCubicPos := L0CubicPosCoeff(lie0);
		lieCubicNeg := L0CubicNegCoeff(lie0);
		liePos1 := LiePart(lieEl, 1);
		lieYCoeff := LiePart(lieEl, 2);
		result := lieEl;
		# Case distinction by root
		if rootG2 = [-2, -1] then
			# Define rho so that liehom(root, a) = rho*x
			rho := LiePart(liehom(root, a), -2);
			# Action on L_{-2} + L_{-1} + DD + Cubic + Cubic' is id
			# Action on xi and zeta
			result := result + 2*rho*lieXiCoeff*LieX;
			result := result + rho*lieZetaCoeff*LieX;
			# Action on L_1
			result := result - rho*BrownNegToLieEmb(liePos1);
			# Action on L_2
			result := result + rho*lieYCoeff*LieXi + rho^2*lieYCoeff*LieX;
			return result;
		elif rootG2 = [2, 1] then
			# Define rho so that liehom(root, a) = rho*y
			rho := LiePart(liehom(root, a), 2);
			# Action on L_{2} + L_{1} + DD + Cubic + Cubic' is id
			# Action on xi and zeta
			result := result - 2*rho*lieXiCoeff*LieY;
			result := result - rho*lieZetaCoeff*LieY;
			# Action on L_{-1}
			result := result + rho*BrownPosToLieEmb(lieNeg1);
			# Action on L_{-2}
			result := result - rho*lieXCoeff*LieXi + rho^2*lieXCoeff*LieY;
			return result;
		elif rootG2[1] = 1 then
			## Components of a
			aLie := liehom(root, a);
			aBrown := LiePart(aLie, 1); # aLie = aBrown_+
			lam := BrownElComPart(aBrown, 1);
			b := BrownElCubicPart(aBrown, 1);
			b2 := BrownElCubicPart(aBrown, 2);
			mu := BrownElComPart(aBrown, 2);
			## Action on L_2 is id
			## Action on L_1
			nu := BrownElComPart(liePos1, 1);
			c := BrownElCubicPart(liePos1, 1);
			c2 := BrownElCubicPart(liePos1, 2);
			rho := BrownElComPart(liePos1, 2);
			result := result + (CubicBiTr(b,c2) - CubicBiTr(c,b2) + mu*nu - lam*rho)*LieY;
			## Action on L0
			# Action on xi and zeta
			result := result - lieXiCoeff*aLie;
			result := result + lieZetaCoeff*LieBrownPosElFromTuple(lam, CubicZero, -b2, -2*mu);
			# Action on Cubic
			c := lieCubicPos;
			result := Sum([
				result,
				-LieBrownPosElFromTuple(Zero(ComRing), lam*c, CubicCross(c,b), CubicBiTr(c, b2)),
				- CubicBiTr(c, CubicAdj(b))*LieY
			]);
			# Action on Cubic'
			c2 := lieCubicNeg;
			result := Sum([
				result,
				LieBrownPosElFromTuple(CubicBiTr(b,c2), CubicCross(c2,b2), mu*c2, Zero(ComRing)),
				- CubicBiTr(CubicAdj(b2), c2)*LieY
			]);
			# Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*dd_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := Sum([
					result,
					scalar*LieBrownPosElFromTuple(
						lam*CubicBiTr(c, c2),
						-JordanD(c, c2, b) + CubicBiTr(c, c2)*b,
						JordanD(c2, c, b2) - CubicBiTr(c, c2)*b2,
						-mu*CubicBiTr(c, c2)
					)
				]);
			od;
			## Action on L_{-1}
			nu := BrownElComPart(lieNeg1, 1);
			c := BrownElCubicPart(lieNeg1, 1);
			c2 := BrownElCubicPart(lieNeg1, 2);
			rho := BrownElComPart(lieNeg1, 2);
			result := Sum([
				result,
				CubicNegToLieEmb(lam*c2 - CubicCross(c, b) + nu*b2),
				-Liedd(b, c2) - Liedd(c, b2),
				(rho*lam - CubicBiTr(b, c2))*(LieXi - LieZeta),
				(CubicBiTr(c, b2) - nu*mu)*LieZeta,
				CubicPosToLieEmb(rho*b - CubicCross(c2, b2) + mu*c),
				LieBrownPosElFromTuple(
					-rho*lam^2 - CubicBiTr(CubicAdj(b), c),
					JordanU(b, c2) + nu*CubicAdj(b2),
					-rho*CubicAdj(b) - JordanU(b2, c),
					CubicBiTr(c2, CubicAdj(b2)) + nu*mu^2
				),
				(-rho*CubicNorm(b) - nu*CubicNorm(b2))*LieY
			]);
			## Action on L_{-2}
			nextSummand := Sum([
				LieBrownNegElFromTuple(lam, b, b2, mu),
				CubicNegToLieEmb(-CubicAdj(b)),
				CubicPosToLieEmb(-CubicAdj(b2)),
				LieBrownPosElFromTuple(-CubicNorm(b), CubicZero, CubicZero, CubicNorm(b2))
			]);
			result := result + lieXCoeff*nextSummand;
			return result;
		elif rootG2[1] = -1 then
			## Components of a
			aLie := liehom(root, a);
			aBrown := LiePart(aLie, -1); # aLie = aBrown_-
			lam := BrownElComPart(aBrown, 1);
			b := BrownElCubicPart(aBrown, 1);
			b2 := BrownElCubicPart(aBrown, 2);
			mu := BrownElComPart(aBrown, 2);
			## Action on L_{-2} is id
			## Action on L_{-1}
			nu := BrownElComPart(lieNeg1, 1);
			c := BrownElCubicPart(lieNeg1, 1);
			c2 := BrownElCubicPart(lieNeg1, 2);
			rho := BrownElComPart(lieNeg1, 2);
			result := result + (CubicBiTr(b,c2) - CubicBiTr(c,b2) + mu*nu - lam*rho)*LieX;
			## Action on L0
			# Action on xi and zeta
			result := result + lieXiCoeff*aLie;
			result := result + lieZetaCoeff*LieBrownNegElFromTuple(2*lam, b, CubicZero, -mu);
			# Action on Cubic
			c := lieCubicPos;
			result := Sum([
				result,
				-LieBrownNegElFromTuple(Zero(ComRing), lam*c, CubicCross(c,b), CubicBiTr(c, b2)),
				- CubicBiTr(c, CubicAdj(b))*LieX
			]);
			# Action on Cubic'
			c2 := lieCubicNeg;
			result := Sum([
				result,
				LieBrownNegElFromTuple(CubicBiTr(b,c2), CubicCross(c2,b2), mu*c2, Zero(ComRing)),
				- CubicBiTr(CubicAdj(b2), c2)*LieX
			]);
			# Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := Sum([
					result,
					scalar*LieBrownNegElFromTuple(
						lam*CubicBiTr(c, c2),
						-JordanD(c, c2, b) + CubicBiTr(c, c2)*b,
						JordanD(c2, c, b2) - CubicBiTr(c, c2)*b2,
						-mu*CubicBiTr(c, c2)
					)
				]);
			od;
			## Action on L_1
			nu := BrownElComPart(liePos1, 1);
			c := BrownElCubicPart(liePos1, 1);
			c2 := BrownElCubicPart(liePos1, 2);
			rho := BrownElComPart(liePos1, 2);
			result := Sum([
				result,
				CubicNegToLieEmb(-lam*c2 + CubicCross(b, c) - nu*b2),
				Liedd(b, c2) + Liedd(c, b2),
				(lam*rho - CubicBiTr(b, c2))*LieZeta,
				(CubicBiTr(c, b2) - mu*nu)*(LieXi - LieZeta),
				CubicPosToLieEmb(-rho*b + CubicCross(b2, c2) - mu*c),
				LieBrownNegElFromTuple(
					rho*lam^2 + CubicBiTr(c, CubicAdj(b)),
					-JordanU(b, c2) - nu*CubicAdj(b2),
					rho*CubicAdj(b) + JordanU(b2, c),
					-CubicBiTr(CubicAdj(b2), c2) - mu^2*nu
				),
				(rho*CubicNorm(b) + nu*CubicNorm(b2))*LieX
			]);
			## Action on L_2
			nextSummand := Sum([
				-LieBrownPosElFromTuple(lam, b, b2, mu),
				CubicNegToLieEmb(-CubicAdj(b)),
				CubicPosToLieEmb(-CubicAdj(b2)),
				LieBrownNegElFromTuple(-CubicNorm(b), CubicZero, CubicZero, CubicNorm(b2))
			]);
			result := result + lieYCoeff*nextSummand;
			return result;
		elif rootG2 = [0, 1] then
			aLie := liehom(root, a);
			aCubic := L0CubicPosCoeff(LiePart(aLie, 0)); # aLie = ad_{aCubic}^+
			## Action on L_2 + L_{-2} + xi + Cubic is id
			## Action on L_1 + L_{-1}
			for sign in [1, -1] do
				if sign = 1 then
					brown := liePos1;
					LieBrownElFromTuple := LieBrownPosElFromTuple;
				else
					brown := lieNeg1;
					LieBrownElFromTuple := LieBrownNegElFromTuple;
				fi;
				lam := BrownElComPart(brown, 1);
				b := BrownElCubicPart(brown, 1);
				b2 := BrownElCubicPart(brown, 2);
				mu := BrownElComPart(brown, 2);
				result := result + LieBrownElFromTuple(
					Zero(ComRing),
					lam*aCubic,
					CubicCross(aCubic, b) + lam*CubicAdj(aCubic),
					CubicBiTr(aCubic, b2) + CubicBiTr(b, CubicAdj(aCubic)) + lam*CubicNorm(aCubic)
				);
			od;
			## Action on zeta
			result := result - lieZetaCoeff*aLie;
			## Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := result - scalar*CubicPosToLieEmb(JordanD(c, c2, aCubic));
			od;
			## Action on Cubic'
			c2 := lieCubicNeg;
			result := result - Liedd(aCubic, c2) + CubicPosToLieEmb(JordanU(aCubic, c2));
			return result;
		elif rootG2 = [0, -1] then
			aLie := liehom(root, a);
			aCubic2 := L0CubicNegCoeff(LiePart(aLie, 0)); # aLie = ad_{aCubic}^+
			## Action on L_2 + L_{-2} +zeta + Cubic' is id
			## Action on L_1 + L_{-1}
			for sign in [1, -1] do
				if sign = 1 then
					brown := liePos1;
					LieBrownElFromTuple := LieBrownPosElFromTuple;
				else
					brown := lieNeg1;
					LieBrownElFromTuple := LieBrownNegElFromTuple;
				fi;
				lam := BrownElComPart(brown, 1);
				b := BrownElCubicPart(brown, 1);
				b2 := BrownElCubicPart(brown, 2);
				mu := BrownElComPart(brown, 2);
				result := result + LieBrownElFromTuple(
					-CubicBiTr(b, aCubic2) + CubicBiTr(CubicAdj(aCubic2), b2) - mu*CubicNorm(aCubic2),
					-CubicCross(aCubic2, b2) + mu*CubicAdj(aCubic2),
					-mu*aCubic2,
					Zero(ComRing)
				);
			od;
			## Action on zeta
			result := result + lieZetaCoeff*aLie;
			## Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := result + scalar*CubicNegToLieEmb(JordanD(c2, c, aCubic2));
			od;
			## Action on Cubic
			c := lieCubicPos;
			result := result + Liedd(c, aCubic2) + CubicNegToLieEmb(JordanU(aCubic2, c));
			return result;
		else
			return fail;
		fi;
	end);
end);

# Default: naive = false.
InstallMethod(GrpRootHomF4NonDiv, [IsList, IsRingElement], function(root, a)
	return GrpRootHomF4NonDiv(root, a, false);
end);

# F4-root homomorphisms which use division. We only use them to test that they coincide
# with GrpRootHomF4NonDiv.
DeclareOperation("GrpRootHomF4Div", [IsList, IsRingElement]);
InstallMethod(GrpRootHomF4Div, [IsList, IsRingElement], function(root, a)
	return F4Exp(LieRootHomF4(root, a));
end);

DeclareOperation("GrpRootHomF4", [IsList, IsRingElement, IsBool]);
DeclareOperation("GrpRootHomF4", [IsList, IsRingElement]);
# Install method for GrpRootHomF4 later because it uses GrpWeylF4

# root: Root in F4.
# sign (optional argument): 1 or -1. Default 1.
# Returns: The standard Weyl element corresponding to root if sign=1, and its inverse otherwise.
GrpStandardWeylF4 := function(root, sign...)
	local inv, one;
	# Handle optional argument
	if Length(sign) = 0 then
		sign := 1;
	else
		sign := sign[1];
		if not sign in [1,-1] then
			Error("Incorrect argument for GrpStandardWeylF4");
			return fail;
		fi;
	fi;
	if root in F4LongRoots then
		one := One(ComRing);
	elif root in F4ShortRoots then
		one := One(ConicAlg);
	else
		return fail;
	fi;
	inv := GrpRootHomF4(-root, -sign*one);
	return inv * GrpRootHomF4(root, sign*one) * inv;
end;


InstallMethod(GrpRootHomF4, [IsList, IsRingElement, IsBool], function(root, a, naive)
	local roothom, roothomNeg, weyl, weylInv, d1, d4, minusRoots, invRoots;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
	if F4RootG2Coord(root) = [0,0] then
		roothom := rootArg -> GrpRootHomF4NonDiv(rootArg, a, naive);
		roothomNeg := rootArg -> GrpRootHomF4NonDiv(rootArg, -a, naive);
		weyl := GrpStandardWeylF4;
		weylInv := x -> GrpStandardWeylF4(x, -1);
		d1 := F4SimpleRoots[1];
		d4 := F4SimpleRoots[4];
		if root = [0, 1, -1, 0] then
			return weylInv(d1) * roothomNeg([-1, 0, 0, 1]) * weyl(d1);
		elif root = [0, -1, 1, 0] then
			return weylInv(d1) * roothomNeg([1, 0, 0, -1]) * weyl(d1);
		elif root = [0, 1, 0, -1] then
			return weylInv(d1) * roothom([-1, 0, 1, 0]) * weyl(d1);
		elif root = [0, -1, 0, 1] then
			return weylInv(d1) * roothom([1, 0, -1, 0]) * weyl(d1);
		elif root = [0, 0, 1, -1] then
			return weylInv(d4) * roothom([0, -1, 0, -1]) * weyl(d4);
		else
			return weylInv(d4) * roothom([0, 1, 0, 1]) * weyl(d4);
		fi;
	else
		return GrpRootHomF4NonDiv(root, a, naive);
	fi;
end);

# Default: naive = false.
InstallMethod(GrpRootHomF4, [IsList, IsRingElement], function(root, a)
	return GrpRootHomF4(root, a, false);
end);
