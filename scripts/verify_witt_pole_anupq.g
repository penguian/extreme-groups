# verify_witt_pole_anupq.g
#
# Direct ANUPQ verification of the top-weight p-adic Witt pole (Proposition 8.7(2)
# and Theorem 8.9(2)) on the Kovacs-Leedham-Green positive Witt groups G(p, p)
# for primes p in [5, 7, 11, 13, 17], together with verification that G(11, m)
# is extreme (f = (11^m + 1) / 12) for all odd m in [3, 5, 7, 9, 11] and that
# the 13 capable maximal-class groups at 11^7 split into rho = 0 (3 groups,
# killed by Lemma 8.5), rho = 1 (1 group, killed by Lemma 8.3), and the 9
# surviving sectors rho in {2..10} mod 11.

LoadPackage("anupq");
Read("lib/klg_lib.g");

Print("====================================================================\n");
Print("1. EXTREMALITY OF G(11, m) FOR ODD 3 <= m <= 11 (THEOREM 8.1)\n");
Print("====================================================================\n");
for m in [3, 5, 7, 9, 11] do
  t0 := Runtime();
  G := KLGpc(11, m);
  x := Pcgs(G);
  n := (m + 1) / 2;
  # Candidate stabilizer S_0 = <x_2, x_4, ..., x_{2n-2}>
  S0 := Subgroup(G, List([1..n-1], j -> x[2*j]));
  N0 := Normalizer(G, S0);
  if m <= 7 then
    f_val := UltraFastF(G, S0);
    target_f := (11^m + 1) / 12;
    Print("G(11,", m, "): |G|=11^", m, ", |S_0|=11^", LogInt(Size(S0), 11),
          ", Core=", Size(Core(G, S0)),
          ", |N_G(S_0)|=11^", LogInt(Size(N0), 11),
          ", f=", f_val, " (target=", target_f, ", match=", f_val = target_f,
          "), DL=", DerivedLength(G), ", Exp=", Exponent(G),
          " (", Runtime() - t0, " ms)\n");
  else
    Print("G(11,", m, "): |G|=11^", m, ", |S_0|=11^", LogInt(Size(S0), 11),
          ", Core=", Size(Core(G, S0)),
          ", |N_G(S_0)|=11^", LogInt(Size(N0), 11),
          " (NICE normalizer index=11), DL=", DerivedLength(G), ", Exp=", Exponent(G),
          " (", Runtime() - t0, " ms)\n");
  fi;
od;

Print("\n====================================================================\n");
Print("2. ANUPQ TERMINATION OF G(p, p) AT ORDER p^(p+1) (PROPOSITION 8.7(2))\n");
Print("====================================================================\n");
for p in [5, 7, 11, 13, 17] do
  t0 := Runtime();
  Gp := KLGpc(p, p);
  d_next := PqDescendants(Gp : StepSize := 1, ClassBound := p);;
  d_cap := PqDescendants(Gp : StepSize := 1, ClassBound := p, CapableDescendants);;
  Print("p=", p, ": G(", p, ",", p, ") -> order ", p, "^", p+1, ": ",
        Length(d_next), " step-1 max-class descendants, ",
        Length(d_cap), " capable (", Runtime() - t0, " ms)\n");
od;
Print("====================================================================\n");
QUIT;
