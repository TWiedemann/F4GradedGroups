### This file contains the definition of the object [ComRing, Cubic, Cubic', ComRing].
### We refer to this object as Brown because if ComRing is a field of characteristic
### not 2 or 3, it as a structurable algebra sometimes called the Brown algebra.
### It parametrizes the 1-part and the (-1)-part of the Lie algebra.

### Elements of Brown are internally represented as lists [t1, c1, c2, t2], and
### this is also how they are displayed. The corresponding
### elements of the Lie algebra are displayed as [t1, c1, c2, t2]_+ or [t1, c1, c2, t2]_-.

# rep: Representation of an element of Brown.
# Returns: Its string representation.
BindGlobal("_BrownRepToString", rep -> String(rep));

BindGlobal("BrownSpec",  rec(
	ElementName := "BrownElement",
	Zero := a -> [Zero(ComRing), CubicZero, CubicZero, Zero(ComRing)],
	# + and - on representations behave just like they should
	Addition := function(a, b)
		return a+b;
	end,
	AdditiveInverse := a -> -a,
	Print := function(a)
		Print(_BrownRepToString(a));
	end,
	MathInfo := IsAdditivelyCommutativeElement
));
BindGlobal("Brown", ArithmeticElementCreator(BrownSpec));

InstallMethod(String, [IsBrownElement], x -> _BrownRepToString(UnderlyingElement(x)));

# ----- Constructors for elements of Brown -----

BindGlobal("BrownZero", Brown(BrownSpec.Zero(fail)));

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

# i: Integer.
# Returns: A list of the generic basic elements of Brown, using indeterminates a_i and t_i.
BindGlobal("BrownGensAsModule", function(i)
	local t, result, gen;
	t := ComRingIndet(i);
	result := [];
	Add(result, BrownElFromTuple(t, CubicZero, CubicZero, Zero(ComRing)));
	Add(result, BrownElFromTuple(Zero(ComRing), CubicZero, CubicZero, t));
	for gen in CubicGensAsModule(i) do
		Add(result, BrownElFromTuple(Zero(ComRing), gen, CubicZero, Zero(ComRing)));
		Add(result, BrownElFromTuple(Zero(ComRing), CubicZero, gen, Zero(ComRing)));
	od;
	return result;
end);

# ----- Getter functions for coefficients of elements of Brown -----

DeclareOperation("BrownElTuple", [IsBrownElement]);
DeclareOperation("BrownElPart", [IsBrownElement, IsInt]);
DeclareOperation("BrownElComPart", [IsBrownElement, IsInt]);
DeclareOperation("BrownElCubicPart", [IsBrownElement, IsInt]);

# brownEl: Element of Brown.
# Returns: List [a, b, c, d] of the entries of brownEl
InstallMethod(BrownElTuple, [IsBrownElement], function(brownEl)
	return UnderlyingElement(brownEl);
end);

# brownEl: Element of Brown.
# i: 1, 2, 3, or 4.
# Returns: i-th component of brownEl.
InstallMethod(BrownElPart, [IsBrownElement, IsInt], function(brownEl, i)
	if i in [1,2,3,4] then
		return UnderlyingElement(brownEl)[i];
	else
		Error("Brown algebra element: Invalid position.");
		return fail;
	fi;
end);

# brownEl: Element of Brown.
# i: 1 or 2.
# Returns: i-th ComRing-component of brownEl.
InstallMethod(BrownElComPart, [IsBrownElement, IsInt], function(brownEl, i)
	if i = 1 then
		return BrownElPart(brownEl, 1);
	elif i = 2 then
		return BrownElPart(brownEl, 4);
	else
		Error("Brown algebra element: Invalid position (ComPart).");
	fi;
end);

# brownEl: Element of Brown.
# i: 1 or 2.
# Returns: i-th ConicAlg-component of brownEl.
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
