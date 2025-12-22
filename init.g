# InitF4Graded(a,b,c,d) initialises the setup of the package with
# ComRing_rank := a, ConicAlg_rank := b, Trace_MaxLength := c and defines
# the variables in user_vargs.g if d = true.
# InitF4Graded() uses (6,4,4,true) as the default values for (a,b,c,d).
DeclareGlobalFunction("InitF4Graded");
# DeclareOperation("InitF4Graded", [IsInt, IsInt, IsInt]);
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
	RereadPackage("F4GradedGroups", "gap/constants.g");
	RereadPackage("F4GradedGroups", "gap/F4-roots.g");
	RereadPackage("F4GradedGroups", "gap/parity_lists.g");
	RereadPackage("F4GradedGroups", "gap/helper.g");
	RereadPackage("F4GradedGroups", "gap/conic_mag.g");
	RereadPackage("F4GradedGroups", "gap/comring.g");
	RereadPackage("F4GradedGroups", "gap/conic.g");
	RereadPackage("F4GradedGroups", "gap/init.g");
	RereadPackage("F4GradedGroups", "gap/cubic.g");
	RereadPackage("F4GradedGroups", "gap/brown.g");
	RereadPackage("F4GradedGroups", "gap/DD.g");
	RereadPackage("F4GradedGroups", "gap/lie0.g");
	RereadPackage("F4GradedGroups", "gap/lie.g");
	RereadPackage("F4GradedGroups", "gap/lie_roothom.g");
	RereadPackage("F4GradedGroups", "gap/group.g");
	RereadPackage("F4GradedGroups", "gap/simplify.g");
	RereadPackage("F4GradedGroups", "gap/chev.g");
	RereadPackage("F4GradedGroups", "gap/test_equal.g");
	RereadPackage("F4GradedGroups", "gap/test_paper.g");
	RereadPackage("F4GradedGroups", "gap/test_additional.g");
	if userVars = true then
		RereadPackage("F4GradedGroups", "gap/user_vars.g");
	fi;
end);
