
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
	local rootG2;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;
	rootG2 := F4RootG2Coord(root);
	if rootG2 = [-2, -1] then
		return LieEndo(function(lieEl)
			local lie0, lieXiCoeff, lieZetaCoeff, liePos1, lieYCoeff, result, rho;
			# Define rho so that LieRootHomF4(root, a) = rho*x
			rho := LiePart(LieRootHomF4(root, a), -2);
			# Components of lieEl
			lie0 := LiePart(lieEl, 0);
			lieXiCoeff := L0XiCoeff(lie0);
			lieZetaCoeff := L0ZetaCoeff(lie0);
			liePos1 := LiePart(lieEl, 1);
			lieYCoeff := LiePart(lieEl, 2);
			result := lieEl;
			# Action on L_{-2} + L_{-1} + DD + Cubic + Cubic' is id
			# Action on xi and zeta
			result := result + 2*rho*lieXiCoeff*LieX;
			result := result + rho*lieZetaCoeff*LieX;
			# Action on L_1
			result := result - rho*BrownNegToLieEmb(liePos1);
			# Action on L_2
			result := result + rho*lieYCoeff*LieXi + rho^2*lieYCoeff*LieX;
			return result;
		end);
	elif rootG2 = [2, 1] then
		return LieEndo(function(lieEl)
			local lie0, lieXiCoeff, lieZetaCoeff, lieNeg1, lieXCoeff, result, rho;
			# Define rho so that LieRootHomF4(root, a) = rho*y
			rho := LiePart(LieRootHomF4(root, a), 2);
			# Components of lieEl
			lieXCoeff := LiePart(lieEl, -2);
			lieNeg1 := LiePart(lieEl, -1);
			lie0 := LiePart(lieEl, 0);
			lieXiCoeff := L0XiCoeff(lie0);
			lieZetaCoeff := L0ZetaCoeff(lie0);
			result := lieEl;
			# Action on L_{2} + L_{1} + DD + Cubic + Cubic' is id
			# Action on xi and zeta
			result := result - 2*rho*lieXiCoeff*LieY;
			result := result - rho*lieZetaCoeff*LieY;
			# Action on L_{-1}
			result := result + rho*BrownPosToLieEmb(lieNeg1);
			# Action on L_{-2}
			result := result - rho*lieXCoeff*LieXi + rho^2*lieXCoeff*LieY;
			return result;
		end);
	elif rootG2 = [1, 0] then
		return LieEndo(function(lieEl)
			local bLie, bBrown, b, lieXCoeff, lieNeg1, lie0, liePos1, lieYCoeff, result,
				nu, rho, c, c2, lieXiCoeff, b2, list, scalar;
			# Use name "b" instead of "a", as in the paper
			bLie := LieRootHomF4(root, a);
			bBrown := LiePart(bLie, 1); # We have bLie = bBrown_+
			b := BrownElCubicPart(bBrown, 1); # We have bBrown = [0, b, 0, 0]
			# Components of lieEl
			lieXCoeff := LiePart(lieEl, -2);
			lieNeg1 := LiePart(lieEl, -1);
			lie0 := LiePart(lieEl, 0);
			liePos1 := LiePart(lieEl, 1);
			lieYCoeff := LiePart(lieEl, 2);
			result := lieEl;
			## Action on zeta and L_2 is id
			## Action on L_{-2}
			result := result + lieXCoeff * (
				LieBrownNegElFromTuple(Zero(ComRing), b, CubicZero, Zero(ComRing))
				- CubicNegToLieEmb(CubicAdj(b))
				- LieBrownPosElFromTuple(CubicNorm(b), CubicZero, CubicZero, Zero(ComRing))
			);
			## Action on L_{-1}
			# Define nu, c, c2, rho as in the paper
			nu := BrownElComPart(lieNeg1, 1);
			rho := BrownElComPart(lieNeg1, 2);
			c := BrownElCubicPart(lieNeg1, 1);
			c2 := BrownElCubicPart(lieNeg1, 2);
			result := Sum([
				result,
				CubicNegToLieEmb(-CubicCross(b, c)),
				CubicPosToLieEmb(rho*b),
				CubicBiTr(b, c2) * (LieZeta-LieXi) - Liedd(b, c2),
				LieBrownPosElFromTuple(
					-CubicBiTr(c, CubicAdj(b)),
					CubicBiTr(b, c2)*b - CubicCross(CubicAdj(b), c2),
					-rho*CubicAdj(b),
					Zero(ComRing)
				),
				-rho*CubicNorm(b)*LieY
			]);
			## Action on L_0
			lieXiCoeff := L0XiCoeff(lie0);
			c := L0CubicPosCoeff(lie0);
			b2 := L0CubicNegCoeff(lie0);
			# Action on xi
			result := result - lieXiCoeff * bLie;
			# Action on Cubic
			result := Sum([
				result,
				- LieBrownPosElFromTuple(Zero(ComRing), CubicZero, CubicCross(b, c), Zero(ComRing)),
				-CubicBiTr(c, CubicAdj(b))*LieY
			]);
			# Action on Cubic'
			result := result
				+ LieBrownPosElFromTuple(CubicBiTr(b, b2), CubicZero, CubicZero, Zero(ComRing));
			# Action on DD
			for list in DDCoeffList(L0DDCoeff(lie0)) do
				# list represents scalar*d_{c, c2}
				scalar := list[1];
				c := list[2];
				c2 := list[3];
				result := Sum([
					result,
					scalar*LieBrownPosElFromTuple(
						Zero(ComRing),
						-JordanD(c, c2, b) + CubicBiTr(c, c2)*b,
						CubicZero, Zero(ComRing)
					)
				]);
			od;
			## Action on L_1
			c2 := BrownElCubicPart(liePos1, 2);
			result := result + CubicBiTr(b, c2)*LieY;
			return result;
		end);
	else
		return fail;
	fi;
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

# InstallMethod(GrpRootHomF4, [IsList, IsRingElement], function(root, a)

# 	if not root in F4Roots then
# 		Error("Root not in F4");
# 		return fail;
# 	fi;
# 	return LieEndo(function(lieEl)

# 		xCoeff := LiePart(lieEl, -2);
# 		brownNeg := LiePart(lieEl, -1);
# 		zero := LiePart(lieEl, 0);
# 		brownPos := LiePart(lieEl, 1);
# 		yCoeff := LiePart(lieEl, 2);
# 	end);
# 	if root = [-2, 0, 0, 0] then
# 		return 
# end);
