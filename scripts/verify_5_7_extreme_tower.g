# verify_5_7_extreme_tower.g
# On each of the 24 extreme order-5^7 class representatives (alpha_3 in {2, 3, 4}), with
# S = <x_4, x_2 * x_3^{k_0}>, k_0 = (alpha_2 + alpha_6) / alpha_3 mod 5, verify:
# - the CKNP extremality equality, subdegree profile, and suborbit regularity,
# - the normalizer-core tower (normalizer chain G = G_0 > G_1 > ... > G_n = S,
#   cores H_i = Core_{G_i}(S) of order p^i, normalizer rigidity N_G(H_i) = G_i,
#   two-point intersection rigidity S cap S^g = H_i, and unique maximal overgroup of S),
# - central and abelian-layer structure: |Z(G)| = 5, Z*S = G_{n-1},
#   and K_0 = Core_G(G_{n-1}) = Z x H_1 = gamma_5(G) elementary abelian of order 25,
# - fixed-point counts of H_i on G/S (p^(n-i) fixed points).

Read("lib/iso_orbits_lib.g");
Read("lib/timings_lib.g");

RunVerify57ExtremeTower := function()
  local isoRecs, reps, p, n, targetF, fails, a, G, x, k0, S, ok, act, P, N, f,
        Pa, orbs, O, Pab, O2, tower, K0, ZG;

  isoRecs := ReadIsoClasses57("scripts/iso_classes.txt");
  reps := List(Filtered(isoRecs, r -> r.rep[3] in [2, 3, 4]), r -> r.rep);
  Print("extreme class representatives: ", Length(reps), "\n");

  p := 5;
  n := 4;
  targetF := ExtremeTargetF(p, 2 * n - 1);
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

    # Exact count of elements with a fixed point and CKNP degree check.
    f := Sum(Filtered(ConjugacyClasses(P), c -> NrMovedPoints(Representative(c)) < N), Size);
    ok := ok and f = targetF and Size(P) = p^(2 * n - 1);

    # Subdegrees and suborbit regularity of the point stabilizer Pa.
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

    # Normalizer-core tower and two-point intersection rigidity.
    ok := ok and VerifyExtremeTower(G, S, p);
    tower := NormalizerCoreTower(G, S);
    ok := ok and ExtremeLayerSieveF(G, tower) = targetF;

    # Central and penultimate-core structure: K_0 = Z(G) x H_1 = gamma_5(G).
    K0 := Core(G, tower.desc[n]);
    ok := ok and IsSubgroup(K0, tower.coresDesc[2]) and K0 = LowerCentralSeries(G)[5]
             and IsElementaryAbelian(K0) and Size(K0) = p^2;
    ZG := Centre(G);
    ok := ok and Size(ZG) = p and ClosureGroup(S, ZG) = tower.desc[n]
             and K0 = ClosureGroup(ZG, tower.coresDesc[2]);

    # Kernel H_i = coresDesc[i] fixes exactly p^(n - (i - 1)) points in G/S (for i = 1..n, |H_i|=p^(i-1)).
    ok := ok and ForAll([1..n], i -> N - NrMovedPoints(Image(act, tower.coresDesc[i])) = p^(n + 1 - i));

    # Unique maximal overgroup of S in G.
    ok := ok and Number(MaximalSubgroups(G), M -> IsSubgroup(M, S)) = 1;
    if not ok then Add(fails, a); fi;
  od;
  Print("failures: ", Length(fails), " ", fails, "\n");
  if Length(reps) <> 24 or Length(fails) > 0 then
    Error("Order-5^7 extreme tower verification failed on ", Length(fails), " representatives!");
  fi;
  Print("finished\n");
  PrintTimingIfEnabled();
end;

RunVerify57ExtremeTower();
QUIT;
