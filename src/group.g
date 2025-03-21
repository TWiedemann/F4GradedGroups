
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

InstallMethod(CallFuncList,
    "Allow function-like syntax for LieEndo",
    [IsLieEndo, IsList],
    function(f, args)
        if Length(args) = 1 and IsLieElement(args[1]) then
            return UnderlyingElement(f)(args[1]);  # Ersetze dies durch die gewünschte Berechnung
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
