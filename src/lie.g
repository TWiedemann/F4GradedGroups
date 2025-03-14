LieZeroString := "0_L";

# rep: Internal representation of an element of L
# Output: A string representing this element
LieRepToString := function(rep)
	local stringList, name;
	stringList := [];
	for name in ["neg2", "neg1", "zero", "pos1", "pos2"] do
		if not IsZero(rep.(name)) then
			Add(stringList, String(rep.(name)));
		fi;
	od;
	return StringSum(stringList);
end;

# Elements of L are represented by records with entries "neg2" (in ComRing),
# "neg1" (in Brown), "zero" (in L0), "pos1" (in Brown) and "pos2" (in ComRing).
LieStruc := rec(
	ElementName := "LieElement",
	Addition := function(a, b)
		return rec(
			neg2 := a.neg2 + b.neg2,
			neg2 := a.neg1 + b.neg1,
			zero := a.zero + b.zero,
			pos1 := a.pos1 + b.pos1,
			pos2 := a.pos2 + b.pos2
		);
	end,
	Zero := a -> rec(
		neg2 := Zero(ComRing),
		neg1 := BrownZero,
		zero := L0Zero,
		pos1 := BrownZero,
		pos2 := Zero(ComRing)
	),
	AdditiveInverse := function(a)
		return rec(
			neg2 := -a.neg2,
			neg2 := -a.neg1,
			zero := -a.zero,
			pos1 := -a.pos1,
			pos2 := -a.pos2
		);
	end,
	Print := function(a)
		Print(LRepToString(a));
	end,
	Multiplication := function(a, b)

	end
);

Lie := ArithmeticElementCreator(LSpec);
LieZero := Lie(LSpec.Zero(fail));

DeclareOperation(LiePart, [IsLieElement, IsInt]);
InstallMethod(LiePart, [IsLieElement, IsInt], function(lieEl, i)
	if i = -2 then
		return UnderlyingElement(lieEl).neg2;
	elif i = -1 then
		return UnderlyingElement(lieEl).neg1;
	elif i = 0 then
		return UnderlyingElement(lieEl).zero;
	elif i = 1 then
		return UnderlyingElement(lieEl).pos1;
	elif i = 2 then
		return UnderlyingElement(lieEl).pos2;
	else
		Error("LiePart: Invalid position");
		return fail;
	fi;
);