mode := "unix";

myFilePath := function(s)
	if mode = "windows" then
		return Concatenation("C:/Users/Torben/Documents/Repositories/F4-graded-groups/src/", s);
	elif mode = "wsl" then
		return Concatenation("/mnt/c/Users/Torben/Documents/Repositories/F4-graded-groups/src/", s);
	else
		return Concatenation("./", s);
	fi;
end;

myUnbind := function(s)
	if IsBoundGlobal(s) then
		MakeReadWriteGlobal(s);
		UnbindGlobal(s);
	fi;
end;

### ----- Global variables -----
## ---- Bools ----
# If _SanitizeImmediately = true, DDSanitizeRep is applied after several transformations which
# may produce unsanitized (but correct) output
_SanitizeImmediately := true;
# If true, the tests which check whether elements lie in ComRing or ConicAlg are skipped
_SkipTests := false;
# If true, the values of ConicAlgMagTr are precomputed and cached.
_CacheTrace := true;
# ---- Ints ----
# ComRing contains indeterminates t_1, ..., t_{ComRing_rank}, g_1, ..., g_3 and
# the norms and traces of elements of ConicAlg
ComRing_rank := 6;
# ConicAlg contains indeterminates a_1, ... a_{ConicAlg_rank} (and their conjugations)
ConicAlg_rank := 2;
# Let t = Trace_MaxLength. For all k <= t, all i_1, ..., i_k in [ 1..ConicAlg_rank ]
# and all possible ways to choose brackets,
# an indeterminate which represents tr(a_{i_1} ... a_{i_t}) will be created.
# Some of these indeterminates are the same because there are identities such as
# tr(xy) = tr(yx) or tr((xy)z) = tr(x(yz)).
# If longer products are needed during the runtime, then an error message is printed.
Trace_MaxLength := 5;
# ---- Precomputed information ----
# Dictionary with precomputed values for all traces. Will be initalised later.
_TrDict := fail;
# List with information about the indeterminates of ComRing in the order in which they
# appear in ComRing. I.e. _ComRingIndetInfo[i] contains information about the i-th indeterminate.
# Each entry is a list [ type, info ] where type is one of the strings "g", "t", "n", "tr"
# and info is additional information: For t_i and g_i, info is i. For n(x) and tr(x),
# info is x (as an element of ConicAlgMag)
_ComRingIndetInfo := fail;
# List of all indeterminates tr(a) and list of the "corresponding" elements a+a' in ConicAlg.
# Used by WithoutTraces().
_ComRingTraceIndets := fail;
_ConicAlgTraces := fail;
# _TrSubIndetList contains trace indeterminates which may be replaced by other terms
# using the relation tr(xy') = tr(x)tr(y) - tr(xy). This relation may be used to replace
# all appearances of a_i' in tr.
# _TrSubValueList[i] is the term by which _TrSubIndetList[i] should be replaced.
_TrSubIndetList := fail;
_TrSubValueList := fail;
# ---- Misc ----
BaseRing := Rationals;
### ----------

# Reread("F4-5Grading.g");
Reread(myFilePath("F4-roots.g"));
Reread(myFilePath("helper.g"));
Reread(myFilePath("conic_mag.g"));
Reread(myFilePath("comring.g"));
Reread(myFilePath("conic.g"));
Reread(myFilePath("init.g"));
myUnbind("IsCubicElement");
Reread(myFilePath("cubic.g"));
myUnbind("IsBrownElement");
Reread(myFilePath("brown.g"));
myUnbind("IsDDElement");
myUnbind("IsL0Element");
myUnbind("IsLieElement");
myUnbind("IsLieEndo");
Reread(myFilePath("DD.g"));
Reread(myFilePath("lie0.g"));
Reread(myFilePath("lie.g"));
myUnbind("IsF4GroupElement");
Reread(myFilePath("group.g"));
Reread(myFilePath("test.g"));
Read(myFilePath("user_vars.g"));