# verify_5_7_consistency_and_types.g
# (1) The consistent presentations of the order-5^7 parametric family G(alpha) are
#     exactly those with alpha_3 + alpha_4 === 1 and alpha_2 === alpha_3 - 1 (mod 5),
#     yielding 625 of the 5^6 tuples.
# (2) Partition by isomorphism class across presentation types:
#       Type II:  alpha_3 = 0 and some presentation has alpha_2 + alpha_6 = 0 -> expected 3
#       Type III: alpha_3 = 1 and some presentation has alpha_2 + alpha_6 = 0 -> expected 25
#       Type I-only / remaining classes                                        -> expected 42
#     Every extreme class (alpha_3 in {2, 3, 4}) contains a Type-I presentation
#     (alpha_2 + alpha_6 <> 0 mod 5), splitting into 9 Type-I-only classes and 15 also
#     containing Type-IV presentations (75 Type-IV tuples total).

Read("lib/iso_orbits_lib.g");
Read("lib/timings_lib.g");

RunVerify57ConsistencyAndTypes := function()
  local al, pred, onlyFirstCount, eqPred, isoRecs, orbits, a3of, zero, c2, c3, c1, ext,
        a3Const, allExtHaveType1, extBothCount, extType1OnlyCount, type4Count;

  al := ConsistentAlphas();
  pred := a -> (a[3] + a[4]) mod 5 = 1 and a[2] = (a[3] - 1) mod 5;
  eqPred := Set(al) = Set(Filtered(Tuples([0..4], 6), pred));
  onlyFirstCount := Length(Filtered(Tuples([0..4], 6), a -> (a[3] + a[4]) mod 5 = 1));
  Print("consistent tuples: ", Length(al), "\n");
  Print("equals {a3+a4=1, a2=a3-1}: ", eqPred, "\n");
  Print("only a3+a4=1 would give: ", onlyFirstCount, " tuples\n");

  isoRecs := ReadIsoClasses57("scripts/iso_classes.txt");
  orbits := List(isoRecs, r -> r.orbit);
  Print("classes: ", Length(orbits), "  presentations: ", Sum(orbits, Length), "\n");
  a3of := o -> o[1][3];
  a3Const := ForAll(orbits, o -> ForAll(o, a -> a[3] = o[1][3]));
  Print("alpha3 constant on classes: ", a3Const, "\n");
  zero := o -> ForAny(o, a -> (a[2] + a[6]) mod 5 = 0);
  c2 := Filtered(orbits, o -> a3of(o) = 0 and zero(o));
  c3 := Filtered(orbits, o -> a3of(o) = 1 and zero(o));
  c1 := Length(orbits) - Length(c2) - Length(c3);
  Print("presentation type counts by class: Type1Rem=", c1, " Type2=", Length(c2),
        " Type3=", Length(c3), "\n");
  ext := Filtered(orbits, o -> a3of(o) in [2, 3, 4]);
  allExtHaveType1 := ForAll(ext, o -> ForAny(o, a -> (a[2] + a[6]) mod 5 <> 0));
  extBothCount := Number(ext, zero);
  extType1OnlyCount := Number(ext, o -> not zero(o));
  type4Count := Number(al, a -> a[3] in [2, 3, 4] and (a[2] + a[6]) mod 5 = 0);
  Print("extreme classes: ", Length(ext), "\n");
  Print("every extreme class has a Type-I presentation: ", allExtHaveType1, "\n");
  Print("extreme classes with ALSO an alpha2+alpha6=0 presentation: ", extBothCount, "\n");
  Print("extreme classes with ONLY Type-I presentations: ", extType1OnlyCount, "\n");
  Print("Type-IV presentations (a3 in {2,3,4} and a2+a6=0): ", type4Count, "\n");

  if Length(al) <> 625 or not eqPred or onlyFirstCount <> 3125
     or Length(orbits) <> 70 or Sum(orbits, Length) <> 625 or not a3Const
     or c1 <> 42 or Length(c2) <> 3 or Length(c3) <> 25
     or Length(ext) <> 24 or not allExtHaveType1
     or extBothCount <> 15 or extType1OnlyCount <> 9 or type4Count <> 75 then
    Error("Order-5^7 consistency or presentation type count verification failed!");
  fi;
  PrintTimingIfEnabled();
end;

RunVerify57ConsistencyAndTypes();
QUIT;
