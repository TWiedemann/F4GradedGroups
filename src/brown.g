# The Brown algebra (ComRing, Cubic, Cubic, ComRing) to which L_{\pm 1} is isomorphic
BrownSpec := rec(
	ElementName := "BrownElement",
	Zero := a -> [Zero(ComRing), CubicZero, CubicZero, Zero(ComRing)],
	Addition := function(a, b)
		return a+b;
	end,
	AdditiveInverse := a -> -a,
	MathInfo := IsAdditivelyCommutativeElement
);
Brown := ArithmeticElementCreator(BrownSpec);

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
InstallOtherMethod(\*, "for ComRingElement and CubicElement", [IsRingElement, IsBrownElement], 2, function(comEl, brownEl)
	ReqComRingEl(comEl);
	return Brown(comEl * UnderlyingElement(brownEl));
end);