# verify_witt_pole_anupq.g
#
# Direct ANUPQ verification of the top-weight p-adic Witt pole on the
# Kovacs-Leedham-Green positive Witt groups G(p, p) for primes p in [5, 7, 11, 13],
# together with verification that G(11, m) is extreme (f = (11^m + 1) / 12) for
# all odd m in [3, 5, 7, 9, 11].
# Note: in part 2, KLGpc(p, p) is re-encoded via PqWeightedPresentation so
# that ANUPQ operates on a weighted p-quotient pcgs matching PQ_AUT_INPUT.

Read("lib/klg_lib.g");
Read("lib/timings_lib.g");
RequirePackage("anupq");

RunVerifyWittPole := function()
  local m, G, x, n, S0, N0, tower, tower_ok, f_val, target_f, p, Gp, d_next, d_cap;

  Print("====================================================================\n");
  Print("1. EXTREMALITY OF G(11, m) FOR ODD 3 <= m <= 11\n");
  Print("====================================================================\n");
  for m in [3, 5, 7, 9, 11] do
    G := KLGpc(11, m);
    x := Pcgs(G);
    n := (m + 1) / 2;
    # Candidate stabilizer S_0 = <x_2, x_4, ..., x_{2n-2}>
    S0 := Subgroup(G, List([1..n-1], j -> x[2 * j]));
    N0 := Normalizer(G, S0);
    tower := NormalizerCoreTower(G, S0);
    tower_ok := VerifyExtremeTower(G, S0, 11);
    # Disjoint-layer fixed-point sum from the tower; cross-check via UltraFastF for m <= 5.
    f_val := ExtremeLayerSieveF(G, tower);
    if m <= 5 then
      tower_ok := tower_ok and (UltraFastF(G, S0) = f_val);
    fi;
    target_f := ExtremeTargetF(11, m);
    Print("G(11,", m, "): |G|=11^", m, ", |S_0|=11^", LogInt(Size(S0), 11),
          ", Core=", Size(Core(G, S0)),
          ", |N_G(S_0)|=11^", LogInt(Size(N0), 11),
          " (index=", Index(N0, S0), ", TOWER=", tower_ok, ")",
          ", f=", f_val, " (target=", target_f, ", match=", f_val = target_f and tower_ok,
          "), DL=", DerivedLength(G), ", Exp=", Exponent(G), "\n");
    if not tower_ok or f_val <> target_f or Size(Core(G, S0)) <> 1 then
      Error("G(11,", m, ") extremality or tower verification failed!");
    fi;
  od;

  Print("\n====================================================================\n");
  Print("2. ANUPQ TERMINATION OF G(p, p) AT ORDER p^(p+1)\n");
  Print("====================================================================\n");
  for p in [5, 7, 11, 13] do
    Gp := PqWeightedPresentation(KLGpc(p, p), p);
    d_cap := PqDescendants(Gp : StepSize := 1, ClassBound := p, CapableDescendants);
    if p <= 7 then
      d_next := PqDescendants(Gp : StepSize := 1, ClassBound := p);
      Print("p=", p, ": G(", p, ",", p, ") -> order ", p, "^", p + 1, ": ",
            Length(d_next), " step-1 max-class descendants, ",
            Length(d_cap), " capable\n");
      if (p = 5 and (Length(d_next) <> 18 or Length(d_cap) <> 1))
         or (p = 7 and (Length(d_next) <> 472 or Length(d_cap) <> 0)) then
        Error("Unexpected descendant count for p = ", p);
      fi;
    else
      Print("p=", p, ": G(", p, ",", p, ") -> order ", p, "^", p + 1, ": ",
            Length(d_cap), " capable step-1 max-class descendants\n");
      if Length(d_cap) <> 0 then
        Error("Unexpected capable descendant for p = ", p);
      fi;
    fi;
  od;
  PrintTimingIfEnabled();
  Print("====================================================================\n");
end;

RunVerifyWittPole();
QUIT;
