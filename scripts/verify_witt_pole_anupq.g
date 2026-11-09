# verify_witt_pole_anupq.g
#
# Direct ANUPQ verification of the top-weight p-adic Witt pole (Proposition 9.2(2)
# and Theorem 9.4(2)) on the Kovacs-Leedham-Green positive Witt groups G(p, p)
# for primes p in [5, 7, 11, 13, 17], together with verification that G(11, m)
# is extreme (f = (11^m + 1) / 12) for all odd m in [3, 5, 7, 9, 11].

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

RunVerifyWittPole := function()
  local m, G, x, n, S0, N0, chain, cur, i, H_chain, nice_ok, f_val, target_f, p, Gp, d_next, d_cap;

  Print("====================================================================\n");
  Print("1. EXTREMALITY OF G(11, m) FOR ODD 3 <= m <= 11 (THEOREM 8.1)\n");
  Print("====================================================================\n");
  for m in [3, 5, 7, 9, 11] do
    G := KLGpc(11, m);
    x := Pcgs(G);
    n := (m + 1) / 2;
    # Candidate stabilizer S_0 = <x_2, x_4, ..., x_{2n-2}>
    S0 := Subgroup(G, List([1..n-1], j -> x[2 * j]));
    N0 := Normalizer(G, S0);
    # Build full normalizer chain S_0 = G_n < G_{n-1} < ... < G_0 = G and verify
    # CKNP Theorem 2E / NICE normalizer, core, and two-point intersection conditions:
    chain := [ S0 ];
    cur := S0;
    for i in [1..n] do
      cur := Normalizer(G, cur);
      Add(chain, cur);
    od;
    H_chain := List([1..n], i -> Core(chain[i + 1], S0));
    nice_ok := (chain[n + 1] = G)
               and ForAll([1..n], i -> Index(chain[i + 1], chain[i]) = 11)
               and ForAll([1..n], i -> Size(H_chain[i]) = 11^(n - i))
               and ForAll([1..n], i -> Normalizer(G, H_chain[i]) = chain[i + 1])
               and ForAll([1..n], i -> ForAll(RightTransversal(chain[i + 1], chain[i]),
                     g -> g in chain[i] or Intersection(S0, S0^g) = H_chain[i]));
    # Disjointness of (H_{i+1} \ H_i)^g across a transversal of G_{i+1} in G (CKNP 2E(d))
    # gives the exact fixed-point element count f(G, S_0); for m <= 5 we also cross-check
    # against UltraFastF(G, S_0).
    f_val := 1 + Sum([1..n-1], i -> Index(G, chain[i + 1]) * (Size(H_chain[i]) - Size(H_chain[i + 1])));
    if m <= 5 then
      nice_ok := nice_ok and (UltraFastF(G, S0) = f_val);
    fi;
    target_f := (11^m + 1) / 12;
    Print("G(11,", m, "): |G|=11^", m, ", |S_0|=11^", LogInt(Size(S0), 11),
          ", Core=", Size(Core(G, S0)),
          ", |N_G(S_0)|=11^", LogInt(Size(N0), 11),
          " (index=", Index(N0, S0), ", NICE=", nice_ok, ")",
          ", f=", f_val, " (target=", target_f, ", match=", f_val = target_f and nice_ok,
          "), DL=", DerivedLength(G), ", Exp=", Exponent(G), "\n");
  od;

  Print("\n====================================================================\n");
  Print("2. ANUPQ TERMINATION OF G(p, p) AT ORDER p^(p+1) (PROPOSITION 9.2(2))\n");
  Print("====================================================================\n");
  for p in [5, 7, 11, 13, 17] do
    Gp := KLGpc(p, p);
    d_next := PqDescendants(Gp : StepSize := 1, ClassBound := p);
    d_cap := PqDescendants(Gp : StepSize := 1, ClassBound := p, CapableDescendants);
    Print("p=", p, ": G(", p, ",", p, ") -> order ", p, "^", p + 1, ": ",
          Length(d_next), " step-1 max-class descendants, ",
          Length(d_cap), " capable\n");
  od;
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunVerifyWittPole();
QUIT;
