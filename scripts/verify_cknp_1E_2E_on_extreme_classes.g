# verify_cknp_1E_2E_on_extreme_classes.g
# On each of the 24 extreme class representatives (alpha_3 in {2, 3, 4}), with
# S = <x_4, x_2 * x_3^{k_0}>, k_0 = (alpha_2 + alpha_6) / alpha_3 mod 5, check:
# - CKNP Theorem 1E(a)-(d) and Theorem 2E(a), (b), (e), (f),
# - Lemma A (N_G(H_i) = G_i),
# - ACPS 4 (|Z(G)| = 5, Z*S = G_3, K_0 = Z x H_1 = gamma_5 elementary abelian),
# - 1982 NICE clauses 1, 4, 5.

Read("lib/alpha_lib.g");
Read("lib/timings_lib.g");

RunVerifyCKNP := function()
  local lines, reps, p, n, fails, a, G, x, k0, S, ok, act, P, N, f,
        Pa, orbs, O, Pab, O2, Gi, i, Hi, K0, ZG;

  lines := SplitString(StringFile("scripts/iso_classes.txt"), "\n");
  lines := Filtered(lines, l -> Length(l) > 0 and l[1] in "0123456789");
  reps := List(lines, l -> EvalString(SplitString(l, ";")[2]));
  reps := Filtered(reps, a -> a[3] in [2, 3, 4]);
  Print("extreme class representatives: ", Length(reps), "\n");

  p := 5;
  n := 4;
  fails := [];
  for a in reps do
    G := DescGroup(a);
    x := AsList(Pcgs(G));
    k0 := ((a[2] + a[6]) * (1 / a[3] mod 5)) mod 5;
    S := Subgroup(G, [x[4], x[2] * x[3]^k0]);
    ok := Size(S) = 125 and Size(Core(G, S)) = 1;
    act := FactorCosetAction(G, S);
    P := Image(act);
    N := NrMovedPoints(P);

    # f = number of elements with a fixed point
    f := Sum(Filtered(ConjugacyClasses(P), c -> NrMovedPoints(Representative(c)) < N), Size);
    ok := ok and f = (p^(2 * n - 1) + 1) / (p + 1);

    # 1E(a)
    ok := ok and Size(P) = p^(2 * n - 1);

    # 1E(b), (c), (d)
    Pa := Stabilizer(P, 1);
    orbs := Orbits(Pa, [1..N]);
    ok := ok and Collected(List(orbs, Length)) = [[1, p], [p, p - 1], [p^2, p - 1], [p^3, p - 1]];
    for O in Filtered(orbs, O -> Length(O) > 1) do
      ok := ok and Size(Image(ActionHomomorphism(Pa, O))) = Length(O);
      Pab := Stabilizer(Pa, O[1]);
      for O2 in Filtered(orbs, O2 -> Length(O2) <= Length(O)) do
        ok := ok and ForAll(O2, b -> ForAll(GeneratorsOfGroup(Pab), g -> b^g = b));
      od;
    od;

    # 2E chain by normalizers
    Gi := [];
    Gi[n + 1] := S;
    for i in [n-1, n-2 .. 0] do
      Gi[i + 1] := Normalizer(G, Gi[i + 2]);
    od;
    ok := ok and Gi[1] = G and ForAll([0..n-1], i -> Index(Gi[i + 1], Gi[i + 2]) = p);
    Hi := List([0..n-1], i -> Core(Gi[i + 1], S));
    ok := ok and ForAll([0..n-1], i -> Size(Hi[i + 1]) = p^i);                       # 2E(a), NICE 3
    K0 := Core(G, Gi[n]);
    ok := ok and IsSubgroup(K0, Hi[2]) and K0 = LowerCentralSeries(G)[5]
             and IsElementaryAbelian(K0) and Size(K0) = p^2;                         # 2E(b), ACPS 4
    ok := ok and ForAll([0..n-1], i -> ForAll(RightTransversal(Gi[i + 1], Gi[i + 2]),
             g -> g in Gi[i + 2] or Intersection(S, S^g) = Hi[i + 1]));              # 2E(f)
    ok := ok and ForAll([0..n-1], i -> Normalizer(G, Hi[i + 1]) = Gi[i + 1]);        # Lemma A, NICE 4, 5
    ZG := Centre(G);
    ok := ok and Size(ZG) = p and ClosureGroup(S, ZG) = Gi[n] and K0 = ClosureGroup(ZG, Hi[2]); # ACPS 4

    # NICE 1: H_i fixes exactly p^(n-i) points
    ok := ok and ForAll([0..n-1], i -> N - NrMovedPoints(Image(act, Hi[i + 1])) = p^(n - i));

    # Overgroups of S form a chain (2E(e)): exactly one maximal subgroup of G contains S
    ok := ok and Number(MaximalSubgroups(G), M -> IsSubgroup(M, S)) = 1;
    if not ok then Add(fails, a); fi;
  od;
  Print("failures: ", Length(fails), " ", fails, "\n");
  if Length(fails) > 0 then
    Error("CKNP 1E/2E verification failed on ", Length(fails), " extreme class representatives!");
  fi;
  Print("finished\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunVerifyCKNP();
QUIT;
