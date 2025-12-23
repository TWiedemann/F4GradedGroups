# InitF4Graded(a,b,c,d) initialises the setup of the package with
# ComRing_rank := a, ConicAlg_rank := b, Trace_MaxLength := c and defines
# the variables in user_vargs.g if d = true.
# InitF4Graded() uses (6,4,4,true) as the default values for (a,b,c,d).
DeclareGlobalFunction("InitF4Graded");
InstallGlobalFunction(InitF4Graded, function(args...)
	local comrank, conicrank, tracelength, s, userVars;
	# Set default values for ComRing_rank, ConicAlg_rank, Trace_MaxLength
	if Length(args) > 0 then
		comrank := args[1];
		conicrank := args[2];
		tracelength := args[3];
		userVars := args[4];
	else
		comrank := 6;
		conicrank := 4;
		tracelength := 4;
		userVars := true;
	fi;
	# If InitF4Graded is called a second time in the same GAP session (not recommended, but
	# "usually" works), then the variables have to be unbound first
	for s in ["ComRing_rank", "ConicAlg_rank", "Trace_MaxLength"] do
		if IsBoundGlobal(s) then
			MakeReadWriteGlobal(s);
			UnbindGlobal(s);
		fi;
	od;
	BindGlobal("ComRing_rank", comrank);
	BindGlobal("ConicAlg_rank", conicrank);
	BindGlobal("Trace_MaxLength", tracelength);
	# Read files
	RereadPackage("F4GradedGroups", "gap/constants.g"); # Global constants of the package
	RereadPackage("F4GradedGroups", "gap/F4-roots.g"); # The root systems F4 and G2
	RereadPackage("F4GradedGroups", "gap/parity_lists.g"); # Stores the parity map of the F4-graded group
	RereadPackage("F4GradedGroups", "gap/helper.g"); # Helper functions, monstly for lists
	RereadPackage("F4GradedGroups", "gap/conic_mag.g"); #
	RereadPackage("F4GradedGroups", "gap/comring.g"); # Commutative ring k = ComRing
	RereadPackage("F4GradedGroups", "gap/conic.g"); # Conic algebra C = Conic
	RereadPackage("F4GradedGroups", "gap/init_trlists.g"); # Initialises some global constants
	RereadPackage("F4GradedGroups", "gap/cubic.g"); # Cubic Jordan matrix algebra
	RereadPackage("F4GradedGroups", "gap/brown.g"); # Brown algebra
	RereadPackage("F4GradedGroups", "gap/DD.g"); # DD
	RereadPackage("F4GradedGroups", "gap/lie0.g"); # L_0
	RereadPackage("F4GradedGroups", "gap/lie.g"); # Lie algebra L
	RereadPackage("F4GradedGroups", "gap/lie_roothom.g"); # Root homomorphisms in L
	RereadPackage("F4GradedGroups", "gap/group.g"); # LieEndo and root homomorphisms in there
	RereadPackage("F4GradedGroups", "gap/simplify.g"); # Simplification functions
	RereadPackage("F4GradedGroups", "gap/chev.g"); # Chevalley-type bases
	RereadPackage("F4GradedGroups", "gap/test_equal.g"); # Equality tests
	if userVars = true then
		RereadPackage("F4GradedGroups", "gap/user_vars.g"); # Additional shortcuts for convenience
	fi;
end);
