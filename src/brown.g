
BrownRepToString := rep -> String(rep);

# Elements of the Brown algebra are represented by lists [ComRing, Cubic, Cubic, ComRing]
BrownSpec := rec(
	ElementName := "BrownElement",
	Zero := a -> [Zero(ComRing), CubicZero, CubicZero, Zero(ComRing)],
	Addition := function(a, b)
		return a+b;
	end,
	Print := function(a)
		Print(BrownRepToString(a));
	end,
	AdditiveInverse := a -> -a,
	MathInfo := IsAdditivelyCommutativeElement
);
Brown := ArithmeticElementCreator(BrownSpec);

InstallMethod(String, [IsBrownElement], x -> BrownRepToString(UnderlyingElement(x)));

## Constructors for elements of Brown

BrownZero := Brown(BrownSpec.Zero(fail));

DeclareOperation("BrownElFromTuple", [IsRingElement, IsCubicElement, IsCubicElement, IsRingElement]);
InstallMethod(BrownElFromTuple, [IsRingElement, IsCubicElement, IsCubicElement, IsRingElement],
	function(a, b, c, d)
		if not ReqComRingEl([a,d]) then
			return fail;
		else
			return Brown([a, b, c, d]);
		fi;
	end
);

## Getters for components

DeclareOperation("BrownElTuple", [IsBrownElement]);
DeclareOperation("BrownElPart", [IsBrownElement, IsInt]);
DeclareOperation("BrownElComPart", [IsBrownElement, IsInt]);
DeclareOperation("BrownElCubicPart", [IsBrownElement, IsInt]);

# Output: List [a, b, c, d] of the entries of brownEl
InstallMethod(BrownElTuple, [IsBrownElement], function(brownEl)
	return UnderlyingElement(brownEl);
end);

InstallMethod(BrownElPart, [IsBrownElement, IsInt], function(brownEl, i)
	if i in [1,2,3,4] then
		return UnderlyingElement(brownEl)[i];
	else
		Error("Brown algebra element: Invalid position.");
		return fail;
	fi;
end);

InstallMethod(BrownElComPart, [IsBrownElement, IsInt], function(brownEl, i)
	if i = 1 then
		return BrownElPart(brownEl, 1);
	elif i = 2 then
		return BrownElPart(brownEl, 4);
	else
		Error("Brown algebra element: Invalid position (ComPart).");
	fi;
end);

InstallMethod(BrownElCubicPart, [IsBrownElement, IsInt], function(brownEl, i)
	if i = 1 then
		return BrownElPart(brownEl, 2);
	elif i = 2 then
		return BrownElPart(brownEl, 3);
	else
		Error("Brown algebra element: Invalid position (CubicPart).");
	fi;
end);

# Scalar multiplication ComRing x Brown -> Brown
InstallOtherMethod(\*, "for ComRingElement and BrownElement", [IsRingElement, IsBrownElement], 2, function(comEl, brownEl)
	ReqComRingEl(comEl);
	return Brown(comEl * UnderlyingElement(brownEl));
end);

# i: Integer.
# Output: A list of the generic basic elements of Brown, using indeterminates a_i and t_i
BrownGensAsModule := function(i)
	local t, result, gen;
	t := ComRingBasicIndet(i);
	result := [];
	Add(result, BrownElFromTuple(t, CubicZero, CubicZero, Zero(ComRing)));
	Add(result, BrownElFromTuple(Zero(ComRing), CubicZero, CubicZero, t));
	for gen in CubicGensAsModule(i) do
		Add(result, BrownElFromTuple(Zero(ComRing), gen, CubicZero, Zero(ComRing)));
		Add(result, BrownElFromTuple(Zero(ComRing), CubicZero, gen, Zero(ComRing)));
	od;
	return result;
end;

## ---- Simplifiers ----

# DeclareOperation("CleanTraces", [IsBrownElement]);
# InstallMethod(CleanTraces, [IsBrownElement], function(brownEl)
# 	return BrownElFromTuple(
# 		CleanTraces(BrownElPart(brownEl, 1)),
# 		CleanTraces(BrownElPart(brownEl, 2)),
# 		CleanTraces(BrownElPart(brownEl, 3)),
# 		CleanTraces(BrownElPart(brownEl, 4))
# 	);
# end);

## Root homomorphisms

DeclareOperation("BrownRootHomF4", [IsList, IsRingElement]);

# root: An element [r1, r2, r3, r4] of F4 with r1 = 1 or r1 = -1.
# a: An element of ConicAlg or of Comring
# Output: An element b of the Brown algebra such that BrownPosToLieEmb(b) is the a-element
# of the [1, r2, r3, r4]-space of Lie and such that BrownNegToLieEmb(b) is the a-element
# of the [-1, r2, r3, r4]-space of Lie. (Note that r1 is ignored)
InstallMethod(BrownRootHomF4, [IsList, IsRingElement], function(root, a)
	if not root in F4Roots then
		Error("Argument is not a root");
		return fail;
	elif not root[1] in [1, -1] then
		Error("BrownRootHomF4 not defined for this root");
		return fail;
	fi;
	if root{[2..4]} = [1,1,1] then
		return BrownElFromTuple(Zero(ComRing), CubicZero, CubicZero, a);
	elif root{[2..4]} = [-1, -1, -1] then
		return BrownElFromTuple(a, CubicZero, CubicZero, Zero(ComRing));
	elif Sum(root{[2..4]}) = 1 then
		return BrownElFromTuple(Zero(ComRing), CubicZero, CubicRootHomF4(root, a), Zero(ComRing));
	else
		return BrownElFromTuple(Zero(ComRing), CubicRootHomF4(root, a), CubicZero, Zero(ComRing));
	fi;
end);