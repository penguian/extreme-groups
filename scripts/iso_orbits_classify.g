# iso_orbits_classify.g
# Full isomorphism classification of the 625 consistent presentations of order 5^7 by exact orbits,
# cross-checking |Aut(G_alpha)| against AutomorphismGroupPGroup for every class representative.

Read("lib/iso_orbits_lib.g");
Read("lib/timings_lib.g");
RequirePackage("autpgrp");

RunIsoOrbitsClassify := function()
  local cons, left, classes, R, A, t, out, i;
  cons := ConsistentAlphas();
  Print("consistent: ", Length(cons), "\n");

  left := ShallowCopy(cons);
  classes := [];
  while Length(left) > 0 do
    R := OrbitAndAut(left[1]);
    if not IsSubset(cons, R.orbit) then Error("orbit leaves the consistent set"); fi;
    if not left[1] in R.orbit then Error("alpha not in own orbit"); fi;
    # Cross-check |Aut| with autpgrp for every representative
    A := AutomorphismGroupPGroup(DescGroup(left[1]));
    if A.size <> R.aut then Error("Aut mismatch at ", left[1]); fi;
    Add(classes, R);
    left := Difference(left, R.orbit);
    Print(Length(classes), ": rep ", R.alpha, " type ", PresentationType57(R.alpha),
          " orbit ", Length(R.orbit), " |Aut| = 5^", Log(R.aut, 5), " (", R.aut,
          ") types in orbit ", Set(R.orbit, PresentationType57),
          " ; remaining ", Length(left), "\n");
  od;

  # Orbits must partition cons (they are equivalence classes)
  if Sum(classes, R -> Length(R.orbit)) <> Length(cons) then Error("orbits overlap"); fi;
  Print("NUMBER OF ISOMORPHISM CLASSES: ", Length(classes), "\n");
  for t in [1..4] do
    Print("type ", t, ": ", Number(classes, R -> PresentationType57(R.alpha) = t), " classes\n");
  od;
  Print("extreme (alpha3 in {2,3,4}): ", Number(classes, R -> R.alpha[3] in [2, 3, 4]), " classes\n");

  out := OutputTextFile("scripts/iso_classes.txt", false);
  SetPrintFormattingStatus(out, false);
  for i in [1..Length(classes)] do
    R := classes[i];
    AppendTo(out, i, ";", R.alpha, ";", PresentationType57(R.alpha), ";",
             Length(R.orbit), ";", R.aut, ";", R.orbit, "\n");
  od;
  CloseStream(out);
  PrintTimingIfEnabled();
end;

RunIsoOrbitsClassify();
QUIT;
