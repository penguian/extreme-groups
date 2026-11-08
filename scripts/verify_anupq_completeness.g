# verify_anupq_completeness.g
# Certified verification that the 1982 parametric family contains EVERY descendant
# of E_5 of order 5^7 and nilpotency class 6.

LoadPackage("anupq");
Read("lib/iso_orbits_lib.g");
Read("lib/timings_lib.g");

RunVerifyAnupqCompleteness := function()
  local F, x1, x2, x3, x4, x5, rels, Q, hom, G, desc, c6, matched_alphas,
        i, d, pcgs, L, G1, g2, cs, y2s, found, r, y2, b,
        lines, orbits, l, p, which_class, a, idx;

  Print("=== Constructing base group E_5 ===\n");
  F := FreeGroup("x1", "x2", "x3", "x4", "x5");
  x1 := F.1; x2 := F.2; x3 := F.3; x4 := F.4; x5 := F.5;
  rels := [ x1^5, x2^5, x3^5, x4^5, x5^5,
    Comm(x2, x1) / x3, Comm(x3, x1) / x4, Comm(x4, x1) / x5, Comm(x5, x1),
    Comm(x3, x2) / x5, Comm(x4, x2), Comm(x5, x2),
    Comm(x4, x3), Comm(x5, x3), Comm(x5, x4) ];
  Q := F / rels;
  hom := EpimorphismPGroup(Q, 5, 10);
  G := Image(hom);

  Print("|E_5| = ", Size(G), ", class = ", NilpotencyClassOfGroup(G), "\n");

  Print("=== Computing descendants of E_5 via ANUPQ (OrderBound 7, ClassBound 6) ===\n");
  desc := PqDescendants(G : OrderBound := 7, ClassBound := 6);
  c6 := Filtered(desc, d -> Size(d) = 78125 and NilpotencyClassOfGroup(d) = 6);
  Print("Total descendants of order 5^7 and class 6 from ANUPQ: ", Length(c6), "\n");

  Print("=== Fitting ANUPQ descendants to the 1982 parametric family ===\n");
  matched_alphas := [];
  for i in [1..Length(c6)] do
    d := c6[i];
    pcgs := Pcgs(d);
    L := LowerCentralSeriesOfGroup(d);
    G1 := TwoStepCentralizer(d);
    g2 := L[2];
    cs := Filtered(ConjugacyClasses(d), C -> not Representative(C) in G1);
    y2s := Filtered(AsList(G1), g -> not g in g2);
    found := false;
    for r in cs do
      for y2 in y2s do
        b := FitPair(pcgs, Representative(r), y2);
        if b <> fail then
          Add(matched_alphas, b);
          found := true;
          break;
        fi;
      od;
      if found then break; fi;
    od;
    if not found then
      Error("c6[", i, "] could not be fitted to family pcp!");
    fi;
  od;
  Print("All ", Length(matched_alphas), " groups from ANUPQ fitted to 1982 family!\n");

  Print("=== Matching fitted alphas to the 70 isomorphism classes ===\n");
  lines := ReadAll(InputTextFile("scripts/iso_classes.txt"));
  lines := SplitString(lines, "\n");
  lines := Filtered(lines, l -> Length(l) > 0);
  orbits := [];
  for l in lines do
    p := SplitString(l, ";");
    Add(orbits, EvalString(p[6]));
  od;

  which_class := [];
  for a in matched_alphas do
    idx := First([1..Length(orbits)], j -> a in orbits[j]);
    if idx = fail then Error("alpha ", a, " not in any of the 70 classes!"); fi;
    Add(which_class, idx);
  od;

  Print("Matched classes count: ", Length(which_class), "\n");
  Print("Unique 1982 isomorphism classes matched: ", Length(Set(which_class)), " of 70\n");
  Print("CONCLUSION: The 1982 parametric family contains EVERY descendant of E_5 of order 5^7 and class 6.\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunVerifyAnupqCompleteness();
QUIT;
