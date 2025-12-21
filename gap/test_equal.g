### This file contains equality test functions for Lie and LieEndo.

# ----- Equality tests on Lie -----

# lieEl1, lieEl2: Elements of Lie.
# print: Bool (default: false).
# Returns: If lieEl1 can be proven to be equal to lieEl2 using Simplify, returns true.
# Otherwise returns false, but they may still be equal.
# If print = true, additional information is printed for the parts which are not equal.
DeclareOperation("TestEquality", [IsLieElement, IsLieElement, IsBool]);
InstallMethod(TestEquality, [IsLieElement, IsLieElement, IsBool], function(lieEl1, lieEl2, print)
	local diff, isEqual, i, part;
	diff := Simplify(lieEl1 - lieEl2);
	isEqual := true;
	for i in [-2..2] do
		part := LiePart(diff, i);
		if not IsZero(part) and not IsZero(WithoutTraces(part)) then
			isEqual := false;
			if print then
				Print(String(i), " part: ", part, "\n");
			fi;
		fi;
	od;
	return isEqual;
end);

DeclareOperation("TestEquality", [IsLieElement, IsLieElement]);
InstallMethod(TestEquality, [IsLieElement, IsLieElement], function(lieEl1, lieEl2)
	return TestEquality(lieEl1, lieEl2, false);
end);

# ----- Equality tests on LieEndo -----

# lieEndo1, lieEndo2: Elements of LieEndo
# genList: List of elements of Lie
# Returns: true if lieEndo1 and lieEndo2 agree on all elements of genList after simplification.
# Otherwise the output is the list of all lists [a, b] where a is an element of genList
# and b = lieEndo1(a) - lieEndo2(a) <> 0.
DeclareOperation("TestEqualityOnGenList", [IsLieEndo, IsLieEndo, IsList]);
InstallMethod(TestEqualityOnGenList, [IsLieEndo, IsLieEndo, IsList], 
	function(lieEndo1, lieEndo2, genList)
		local gen, test, errorList;
		errorList := [];
		for gen in genList do
			test := Simplify(lieEndo1(gen) - lieEndo2(gen));
			if not IsZero(test) and not IsZero(WithoutTraces(test)) then
				Add(errorList, [gen, test]);
			fi;
		od;
		if IsEmpty(errorList) then
			return true;
		else
			return errorList;
		fi;
	end
);

# TestEquality(f, g, comIndetNum, conicIndetNum) calls
# TestEqualityOnGenList(f, g, LieGensAsLie(comIndetNum, conicIndetNum)).
# If only one integer n is provided, then TestEquality(f, g, n, n) is called.
# If no integer is provided, then TestEquality(f, g, ComRing_rank, ConicAlg_rank)
# is called.
# Uses indeterminates t_comIndetNum and a_conicIndetNum
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsInt, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo, IsInt]);
DeclareOperation("TestEquality", [IsLieEndo, IsLieEndo]);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsInt, IsInt],
	function(lieEndo1, lieEndo2, comIndetNum, conicIndetNum)
		local genList;
		genList := LieGensAsLie(comIndetNum, conicIndetNum);
		return TestEqualityOnGenList(lieEndo1, lieEndo2, genList);
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo, IsInt], 
	function(lieEndo1, lieEndo2, indetNum)
		return TestEquality(lieEndo1, lieEndo2, indetNum, indetNum);
	end
);

InstallMethod(TestEquality, [IsLieEndo, IsLieEndo], 
	function(lieEndo1, lieEndo2)
		return TestEquality(lieEndo1, lieEndo2, ComRing_rank, ConicAlg_rank);
	end
);

# Like TestEquality, but uses LieGensAsModule in place of LieGensAsLie.
# Uses indeterminates t_comIndetNum, a_conicIndetNum AND a_{conicIndetNum+1}
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo, IsInt, IsInt]);
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo, IsInt]);
DeclareOperation("TestEqualityOnModuleGens", [IsLieEndo, IsLieEndo]);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo, IsInt, IsInt],
	function(lieEndo1, lieEndo2, comIndetNum, conicIndetNum)
		local genList;
		genList := LieGensAsModule(comIndetNum, conicIndetNum);
		return TestEqualityOnGenList(lieEndo1, lieEndo2, genList);
	end
);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo, IsInt], 
	function(lieEndo1, lieEndo2, indetNum)
		return TestEqualityOnModuleGens(lieEndo1, lieEndo2, indetNum, indetNum);
	end
);

InstallMethod(TestEqualityOnModuleGens, [IsLieEndo, IsLieEndo], 
	function(lieEndo1, lieEndo2)
		return TestEqualityOnModuleGens(lieEndo1, lieEndo2, ComRing_rank, ConicAlg_rank-1);
	end
);

# relations: A list of lists [g1, g2] where g1, g2 are automorphisms of Lie.
# Returns: A list of all elements of ComRing, ConicAlg and L0 which have to be proven
# by hand to be zero to verify that g1 = g2 for all [g1, g2] \in relations.
# Uses indeterminates t_{ComRing_rank}, a_{ConicAlg_rank}.
TestEqualityPiecesOnList := function(relations)
	local rel, test, error, part, i, j, result, part2, summands, summand, a;
	result := [];
	for rel in relations do
		test := TestEquality(rel[1], rel[2]);
		if test <> true then
			for error in test do
				# error[1] contains the Lie algebra generator on which rel[1] and rel[2]
				# differ, which is not interesting.
				# error[2] is the Lie algebra element which must be proven by hand to be zero.
				for i in [-2..2] do
					# Decompose error[2] in its parts
					part := LiePart(error[2], i);
					if i=1 or i=-1 then
						# part lies in Brown, and is thus further decomposed
						for j in [1,2] do
							part2 := BrownElComPart(part, j); # \in ComRing
							if not IsZero(part2) then
								Add(result, part2);
							fi;
							part2 := BrownElCubicPart(part, j); # \in Cubic
							# Add all non-zero components of part2 to result
							summands := Summands(part2);
							for summand in summands do
								# summand = [i, j, a], represents a[ij]
								a := summand[3]; # \in ComRing or ConicAlg
								if summand[1] = summand[2] then # a \in ComRing
									if not IsZero(a) then
										Add(result, a);
									fi;
								else # a \in ConicAlg
									if not IsZero(a) and not IsZero(WithoutTraces(a)) then
										Add(result, a);
									fi;
								fi;
							od;
						od;
					elif not IsZero(part) then
						# part lies in ComRing
						Add(result, part);
					fi;
				od;
			od;
		fi;
	od;
	return result;
end;

# Like TestEqualityPiecesOnList, but only one relation "term1=term2" is tested.
TestEqualityPieces := function(term1, term2)
	return TestEqualityPiecesOnList([[term1, term2]]);
end;
