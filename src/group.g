
# Elements of F4Group are represented by functions from Lie to Lie
LieEndoSpec := rec(
	ElementName := "LieEndo",
	Zero := a -> function(x)
		if not IsLieElement(x) then
			Error("Function only defined on elements of Lie");
			return fail;
		else
			return LieZero;
		fi;
	end,
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

DeclareOperation("F4Exp", [IsLieElement]);
DeclareOperation("F4Exp", [IsLieElement, IsInt]);

# TODO: Cut off more unnecessary computations

# a: Element of Lie
# n: Integer, n > 0
# Output: \sum_{i=0}^n (1/i!) * ad_a^i (as an element of F4Group)
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

## ------- Root homomorphisms ----
DeclareOperation("GrpRootHomF4", [IsList, IsRingElement]);
InstallMethod(GrpRootHomF4, [IsList, IsRingElement], function(root, a)
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
	return F4Exp(LieRootHomF4(root, a));
end);

DeclareOperation("GrpRootHomF4NonDiv", [IsList, IsRingElement]);
InstallMethod(GrpRootHomF4NonDiv, [IsList, IsRingElement], function(root, a)
	local rootG2, lieXCoeff, lieNeg1, lie0, lieDDCoeffList, lieXiCoeff, lieZetaCoeff,
		liePos1, lieYCoeff, result, rho, b, bBrown, bLie, b2, c, c2, nu, scalar,
		list, lieCubicNeg, lieCubicPos, aLie, aBrown, lam, mu, nextSummand,
		aCubic, aCubic2, sign, brown, LieBrownElFromTuple;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
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
			# Define rho so that LieRootHomF4(root, a) = rho*x
			rho := LiePart(LieRootHomF4(root, a), -2);
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
			# Define rho so that LieRootHomF4(root, a) = rho*y
			rho := LiePart(LieRootHomF4(root, a), 2);
			# Action on L_{2} + L_{1} + DD + Cubic + Cubic' is id
			# Action on xi and zeta
			result := result - 2*rho*lieXiCoeff*LieY;
			result := result - rho*lieZetaCoeff*LieY;
			# Action on L_{-1}
			result := result + rho*BrownPosToLieEmb(lieNeg1);
			# Action on L_{-2}
			result := result - rho*lieXCoeff*LieXi + rho^2*lieXCoeff*LieY;
			return result;
		# Uses section 6
		elif rootG2[1] = 1 then
			## Components of a
			aLie := LieRootHomF4(root, a);
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
				(lam*CubicBiTr(c,b2) - CubicBiTr(c, CubicAdj(b)))*LieY
			]);
			# Action on Cubic'
			c2 := lieCubicNeg;
			result := Sum([
				result,
				LieBrownPosElFromTuple(CubicBiTr(b,c2), CubicCross(c2,b2), mu*c2, Zero(ComRing)),
				(mu*CubicBiTr(b, c2) - CubicBiTr(CubicAdj(b2), c2))*LieY
			]);
			# Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
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
					),
					scalar * Sum([
						CubicBiTr(JordanD(c, c2, b), b2),
						-CubicBiTr(b, b2)*CubicBiTr(c, c2),
						lam*mu*CubicBiTr(c, c2)
					]) * LieY
				]);
			od;
			## For the action on L_{-1} + L_{-2}, we need a case distinction on root
			## Action on L_{-1}
			nu := BrownElComPart(lieNeg1, 1);
			c := BrownElCubicPart(lieNeg1, 1);
			c2 := BrownElCubicPart(lieNeg1, 2);
			rho := BrownElComPart(lieNeg1, 2);
			if rootG2[2] = -1 then
				nextSummand := Sum([
					lam*CubicNegToLieEmb(c2) + rho*lam*(LieXi-LieZeta),
					-LieBrownPosElFromTuple(rho*lam^2, CubicZero, CubicZero, Zero(ComRing))
				]);
			elif rootG2[2] = 0 then
				nextSummand := Sum([
					-CubicNegToLieEmb(CubicCross(c, b)) - CubicBiTr(b, c2)*(LieXi-LieZeta),
					-Liedd(b, c2),
					rho*CubicPosToLieEmb(b),
					LieBrownPosElFromTuple(
						-CubicBiTr(CubicAdj(b), c),
						JordanU(b, c2),
						-rho*CubicAdj(b),
						Zero(ComRing)
					),
					-rho*CubicNorm(b)*LieY
				]);
			elif rootG2[2] = 1 then
				nextSummand := Sum([
					nu*CubicNegToLieEmb(b2) - CubicPosToLieEmb(CubicCross(c2, b2)),
					CubicBiTr(c, b2)*LieZeta - Liedd(c, b2),
					LieBrownPosElFromTuple(
						Zero(ComRing),
						nu*CubicAdj(b2),
						-JordanU(b2, c),
						CubicBiTr(c2, CubicAdj(b2))
					),
					-nu*CubicNorm(b2)*LieY
				]);
			else
				nextSummand := Sum([
					-nu*mu*LieZeta + mu*CubicPosToLieEmb(c),
					LieBrownPosElFromTuple(Zero(ComRing), CubicZero, CubicZero, nu*mu^2)
				]);
			fi;
			result := result + nextSummand;
			## Action on L_{-2}
			if rootG2[2] = -1 then
				nextSummand := LieBrownNegElFromTuple(lam, CubicZero, CubicZero, Zero(ComRing));
			elif rootG2[2] = 0 then
				nextSummand := Sum([
					LieBrownNegElFromTuple(Zero(ComRing), b, CubicZero, Zero(ComRing)),
					-CubicNegToLieEmb(CubicAdj(b)),
					-LieBrownPosElFromTuple(CubicNorm(b), CubicZero, CubicZero, Zero(ComRing))
				]);
			elif rootG2[2] = 1 then
				nextSummand := Sum([
					LieBrownNegElFromTuple(Zero(ComRing), CubicZero, b2, Zero(ComRing)),
					-CubicPosToLieEmb(CubicAdj(b2)),
					LieBrownNegElFromTuple(Zero(ComRing), CubicZero, CubicZero, CubicNorm(b2))
				]);
			else
				nextSummand := LieBrownNegElFromTuple(Zero(ComRing), CubicZero, CubicZero, mu);
			fi;
			result := result + lieXCoeff*nextSummand;
			return result;
		elif rootG2[1] = -1 then
			## Components of a
			aLie := LieRootHomF4(root, a);
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
				(lam*CubicBiTr(c,b2) - CubicBiTr(c, CubicAdj(b)))*LieX
			]);
			# Action on Cubic'
			c2 := lieCubicNeg;
			result := Sum([
				result,
				LieBrownNegElFromTuple(CubicBiTr(b,c2), CubicCross(c2,b2), mu*c2, Zero(ComRing)),
				(mu*CubicBiTr(b, c2) - CubicBiTr(CubicAdj(b2), c2))*LieX
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
					),
					scalar * Sum([
						CubicBiTr(JordanD(c, c2, b), b2),
						-CubicBiTr(b, b2)*CubicBiTr(c, c2),
						lam*mu*CubicBiTr(c, c2)
					]) * LieX
				]);
			od;
			## For the action on L_1 + L_2, we need a case distinction on root
			## Action on L_1
			nu := BrownElComPart(liePos1, 1);
			c := BrownElCubicPart(liePos1, 1);
			c2 := BrownElCubicPart(liePos1, 2);
			rho := BrownElComPart(liePos1, 2);
			if rootG2[2] = -2 then
				nextSummand := Sum([
					-lam*CubicNegToLieEmb(c2) + rho*lam*LieZeta,
					LieBrownNegElFromTuple(rho*lam^2, CubicZero, CubicZero, Zero(ComRing))
				]);
			elif rootG2[2] = -1 then
				nextSummand := Sum([
					CubicNegToLieEmb(CubicCross(b, c)) - CubicBiTr(b, c2)*LieZeta,
					Liedd(b, c2),
					-rho*CubicPosToLieEmb(b),
					LieBrownNegElFromTuple(
						CubicBiTr(c, CubicAdj(b)),
						-JordanU(b, c2),
						rho*CubicAdj(b),
						Zero(ComRing)
					),
					rho*CubicNorm(b)*LieX
				]);
			elif rootG2[2] = 0 then
				nextSummand := Sum([
					-nu*CubicNegToLieEmb(b2) + CubicPosToLieEmb(CubicCross(c2, b2)),
					CubicBiTr(c, b2)*(LieXi-LieZeta) + Liedd(c, b2),
					LieBrownNegElFromTuple(
						Zero(ComRing),
						-nu*CubicAdj(b2),
						JordanU(b2, c),
						-CubicBiTr(CubicAdj(b2), c2)
					),
					nu*CubicNorm(b2)*LieX
				]);
			else
				nextSummand := Sum([
					nu*mu*(LieZeta-LieXi) - mu*CubicPosToLieEmb(c),
					-LieBrownNegElFromTuple(Zero(ComRing), CubicZero, CubicZero, mu*nu^2)
				]);
			fi;
			result := result + nextSummand;
			## Action on L_{-2}
			if rootG2[2] = -2 then
				nextSummand := -LieBrownPosElFromTuple(lam, CubicZero, CubicZero, Zero(ComRing));
			elif rootG2[2] = -1 then
				nextSummand := Sum([
					-LieBrownPosElFromTuple(Zero(ComRing), b, CubicZero, Zero(ComRing)),
					-CubicNegToLieEmb(CubicAdj(b)),
					-LieBrownNegElFromTuple(CubicNorm(b), CubicZero, CubicZero, Zero(ComRing))
				]);
			elif rootG2[2] = 0 then
				nextSummand := Sum([
					-LieBrownPosElFromTuple(Zero(ComRing), CubicZero, b2, Zero(ComRing)),
					-CubicPosToLieEmb(CubicAdj(b2)),
					LieBrownNegElFromTuple(Zero(ComRing), CubicZero, CubicZero, CubicNorm(b2))
				]);
			else
				nextSummand := -LieBrownNegElFromTuple(Zero(ComRing), CubicZero, CubicZero, mu);
			fi;
			result := result + lieYCoeff*nextSummand;
			return result;
		elif rootG2 = [0, 1] then
			aLie := LieRootHomF4(root, a);
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
			result := result - aLie;
			## Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := result - JordanD(c, c2, aCubic);
			od;
			## Action on Cubic'
			c2 := lieCubicNeg;
			result := result - Liedd(a, c2) + CubicPosToLieEmb(JordanU(a, c2));
			return result;
		elif rootG2 = [0, -1] then
			aLie := LieRootHomF4(root, a);
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
					CubicCross(aCubic2, b2) + mu*CubicAdj(aCubic2),
					mu*aCubic2,
					Zero(ComRing)
				);
			od;
			## Action on zeta
			result := result + aLie;
			## Action on DD
			for list in lieDDCoeffList do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := result + JordanD(c2, c, aCubic2);
			od;
			## Action on Cubic
			c := lieCubicPos;
			result := result + Liedd(c, aCubic2) - CubicNegToLieEmb(JordanU(aCubic2, c));
			return result;
		# Old version using section 4
		# elif rootG2 = [1, 0] then
		# 	# Use name "b" instead of "a", as in the paper
		# 	bLie := LieRootHomF4(root, a);
		# 	bBrown := LiePart(bLie, 1); # We have bLie = bBrown_+
		# 	b := BrownElCubicPart(bBrown, 1); # We have bBrown = [0, b, 0, 0]
		# 	## Action on zeta and L_2 is id
		# 	## Action on L_{-2}
		# 	result := result + lieXCoeff * (
		# 		LieBrownNegElFromTuple(Zero(ComRing), b, CubicZero, Zero(ComRing))
		# 		- CubicNegToLieEmb(CubicAdj(b))
		# 		- LieBrownPosElFromTuple(CubicNorm(b), CubicZero, CubicZero, Zero(ComRing))
		# 	);
		# 	## Action on L_{-1}
		# 	# Define nu, c, c2, rho as in the paper
		# 	nu := BrownElComPart(lieNeg1, 1);
		# 	rho := BrownElComPart(lieNeg1, 2);
		# 	c := BrownElCubicPart(lieNeg1, 1);
		# 	c2 := BrownElCubicPart(lieNeg1, 2);
		# 	result := Sum([
		# 		result,
		# 		CubicNegToLieEmb(-CubicCross(b, c)),
		# 		CubicPosToLieEmb(rho*b),
		# 		CubicBiTr(b, c2) * (LieZeta-LieXi) - Liedd(b, c2),
		# 		LieBrownPosElFromTuple(
		# 			-CubicBiTr(c, CubicAdj(b)),
		# 			CubicBiTr(b, c2)*b - CubicCross(CubicAdj(b), c2),
		# 			-rho*CubicAdj(b),
		# 			Zero(ComRing)
		# 		),
		# 		-rho*CubicNorm(b)*LieY
		# 	]);
		# 	## Action on L_0
		# 	lieXiCoeff := L0XiCoeff(lie0);
		# 	c := L0CubicPosCoeff(lie0);
		# 	b2 := L0CubicNegCoeff(lie0);
		# 	# Action on xi
		# 	result := result - lieXiCoeff * bLie;
		# 	# Action on Cubic
		# 	result := Sum([
		# 		result,
		# 		- LieBrownPosElFromTuple(Zero(ComRing), CubicZero, CubicCross(b, c), Zero(ComRing)),
		# 		-CubicBiTr(c, CubicAdj(b))*LieY
		# 	]);
		# 	# Action on Cubic'
		# 	result := result
		# 		+ LieBrownPosElFromTuple(CubicBiTr(b, b2), CubicZero, CubicZero, Zero(ComRing));
		# 	# Action on DD
		# 	for list in DDCoeffList(L0DDCoeff(lie0)) do
		# 		# list represents scalar*d_{c, c2}
		# 		scalar := list[1];
		# 		c := list[2];
		# 		c2 := list[3];
		# 		result := Sum([
		# 			result,
		# 			scalar*LieBrownPosElFromTuple(
		# 				Zero(ComRing),
		# 				-JordanD(c, c2, b) + CubicBiTr(c, c2)*b,
		# 				CubicZero, Zero(ComRing)
		# 			)
		# 		]);
		# 	od;
		# 	## Action on L_1
		# 	c2 := BrownElCubicPart(liePos1, 2);
		# 	result := result + CubicBiTr(b, c2)*LieY;
		# 	return result;
		else
			return fail;
		fi;
	end);
end);

DeclareOperation("GrpWeylF4", [IsList, IsRingElement, IsRingElement]);
InstallMethod(GrpWeylF4, [IsList, IsRingElement, IsRingElement], function(root, a, b)
	local inv;
	inv := GrpRootHomF4(-root, b);
	return inv * GrpRootHomF4(root, a) * inv;
end);

DeclareOperation("GrpWeylF4", [IsList, IsRingElement]);
InstallMethod(GrpWeylF4, [IsList, IsRingElement], function(root, a)
	return GrpWeylF4(root, a, a); # For (some) long roots, we need a, a. For short roots, this is not yet clear.
end);

DeclareOperation("GrpStandardWeylF4", [IsList]);
InstallMethod(GrpStandardWeylF4, [IsList], function(root)
	local one;
	if root in F4LongRoots then
		one := One(ComRing);
	else
		one := One(ConicAlg);
	fi;
	return GrpWeylF4(root, one, -one);
end);

DeclareOperation("GrpStandardWeylInvF4", [IsList]);
InstallMethod(GrpStandardWeylInvF4, [IsList], function(root)
	local one;
	if root in F4LongRoots then
		one := One(ComRing);
	else
		one := One(ConicAlg);
	fi;
	return GrpWeylF4(root, -one, one);
end);

DeclareOperation("GrpWeylOneF4", [IsList]);
InstallMethod(GrpWeylOneF4, [IsList], function(root)
	if root in F4LongRoots then
		return GrpWeylF4(root, One(ComRing));
	elif root in F4ShortRoots then
		return GrpWeylF4(root, One(ConicAlg));
	else
		return fail;
	fi;
end);

DeclareOperation("GrpWeylOneInvF4", [IsList]);
InstallMethod(GrpWeylOneInvF4, [IsList], function(root)
	if root in F4LongRoots then
		return GrpWeylF4(root, -One(ComRing));
	elif root in F4ShortRoots then
		return GrpWeylF4(root, -One(ConicAlg));
	else
		return fail;
	fi;
end);
