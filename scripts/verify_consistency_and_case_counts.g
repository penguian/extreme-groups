# verify_consistency_and_case_counts.g
# (1) The consistent presentations of the 1982 descendant pcp are exactly those with
#       alpha_3 + alpha_4 = 1  and  alpha_2 = alpha_3 - 1  (mod 5),  625 of the 5^6 tuples.
# (2) The 1982 three-case split, counted by isomorphism class:
#       Case 2: alpha_3 = 0 and some presentation has alpha_2 + alpha_6 = 0  -> expected 3
#       Case 3: alpha_3 = 1 and some presentation has alpha_2 + alpha_6 = 0  -> expected 25
#       Case 1: all remaining classes                                        -> expected 42
#     and every extreme class (alpha_3 in {2, 3, 4}) has a Case-1 presentation (alpha_2 + alpha_6 <> 0).

Read("lib/alpha_lib.g");
Read("lib/timings_lib.g");

RunVerifyConsistencyAndCaseCounts := function()
  local al, pred, lines, orbits, a3of, zero, c2, c3, c1, ext;
  al := ConsistentAlphas();
  pred := a -> (a[3] + a[4]) mod 5 = 1 and a[2] = (a[3] - 1) mod 5;
  Print("consistent tuples: ", Length(al), "\n");
  Print("equals {a3+a4=1, a2=a3-1}: ",
        Set(al) = Set(Filtered(Tuples([0..4], 6), pred)), "\n");
  Print("only a3+a4=1 would give: ",
        Length(Filtered(Tuples([0..4], 6), a -> (a[3] + a[4]) mod 5 = 1)), " tuples\n");

  lines := SplitString(StringFile("scripts/iso_classes.txt"), "\n");
  lines := Filtered(lines, l -> Length(l) > 0 and l[1] in "0123456789");
  orbits := List(lines, l -> EvalString(SplitString(l, ";")[6]));
  Print("classes: ", Length(orbits), "  presentations: ", Sum(orbits, Length), "\n");
  a3of := o -> o[1][3];
  Print("alpha3 constant on classes: ", ForAll(orbits, o -> ForAll(o, a -> a[3] = o[1][3])), "\n");
  zero := o -> ForAny(o, a -> (a[2] + a[6]) mod 5 = 0);
  c2 := Filtered(orbits, o -> a3of(o) = 0 and zero(o));
  c3 := Filtered(orbits, o -> a3of(o) = 1 and zero(o));
  c1 := Length(orbits) - Length(c2) - Length(c3);
  Print("1982 case counts by class: Case1=", c1, " Case2=", Length(c2),
        " Case3=", Length(c3), "\n");
  ext := Filtered(orbits, o -> a3of(o) in [2, 3, 4]);
  Print("extreme classes: ", Length(ext), "\n");
  Print("every extreme class has a Case-1 presentation: ",
        ForAll(ext, o -> ForAny(o, a -> (a[2] + a[6]) mod 5 <> 0)), "\n");
  Print("extreme classes with ALSO an alpha2+alpha6=0 presentation: ", Number(ext, zero), "\n");
  Print("extreme classes with ONLY Case-1 presentations: ", Number(ext, o -> not zero(o)), "\n");
  Print("presentations with a3 in {2,3,4} and a2+a6=0 (in no 1982 case): ",
        Number(al, a -> a[3] in [2, 3, 4] and (a[2] + a[6]) mod 5 = 0), "\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunVerifyConsistencyAndCaseCounts();
QUIT;
