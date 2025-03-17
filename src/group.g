
# Elements of F4Group are represented by functions from Lie to Lie
F4GroupSpec := rec(
	ElementName := "F4GroupElement",
	One := a -> function(x)
		if not IsLieElement(x) then
			Error("Function only defined on elements of Lie");
			return fail;
		else
			return x;
		fi;
	end,
	Multiplication := function(f, g)
		return x -> f(g(x));
	end
);

F4Group := ArithmeticElementCreator(F4GroupSpec);

# Only works for elements a of the root space because they satisfy ad_a^5 = 0.
DeclareOperation("F4Exp", [IsLieElement]);
DeclareOperation("F4Exp", [IsLieElement, IsInt]);

# a: Element of Lie
# n: Integer, n > 0
# Output: \sum_{i=0}^n (1/i!) * ad_a^i (as an element of F4Group)
InstallMethod(F4Exp, [IsLieElement, IsInt], function(a, n)
	return F4Group(function(x)
		local lastSummand, result, i;
		lastSummand := x;
		result := x;
		for i in [1..n] do
			lastSummand := (1/n) * (a * lastSummand);
			result := result + lastSummand;
		od;
		return result;
	end);
end);
# For elements a of F4-root spaces, we know that ad_a^5 = 0.
InstallMethod(F4Exp, [IsLieElement], a -> F4Exp(a, 4));

