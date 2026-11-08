# verify_extreme_7_9.g
# Self-contained verification of an extreme permutation group of order 7^9.
# Discovered on 12 October 2026.
# Group lineage: G(7,5) -> g1 (order 7^6) -> d7[15] (order 7^7) -> Child 13 (order 7^8) -> Group 1 (order 7^9).
# Stabilizer: S = <x4, x2*x3> of order 7^4 = 2401, Core_G(S) = 1.
# Degree: d = [G:S] = 7^5 = 16807.
# Extremality: (p+1)*f(G,S) = |G| + 1 <=> 8 * 5044201 = 40353608.

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

RunVerifyExtreme79 := function()
  local t_start, G75, des75_1, g1, des_g1, G15, des8, c13, des9, G,
        x, S, f, deg, dc, subdegs, expected_subdegs, regular_ok,
        G_chain, cur, i, H_chain;

  t_start := Runtime();

  # 1. Construct root G(7,5) and advance down coclass-1 spine
  G75 := KLGpc(7, 5);
  des75_1 := PqDescendants(G75 : StepSize := 1);
  g1 := des75_1[1];
  des_g1 := PqDescendants(g1 : StepSize := 1);
  G15 := des_g1[15];
  des8 := PqDescendants(G15 : StepSize := 1);
  c13 := des8[13];
  des9 := PqDescendants(c13 : StepSize := 1);
  G := des9[1];

  x := Pcgs(G);
  S := Subgroup(G, [x[4], x[2] * x[3]]);

  Print("====================================================================\n");
  Print("VERIFICATION OF EXTREME PERMUTATION GROUP OF ORDER 7^9\n");
  Print("====================================================================\n");
  Print("Order |G|            : ", Size(G), " = 7^", Log(Size(G), 7), "\n");
  Print("Nilpotency class     : ", NilpotencyClassOfGroup(G), " (maximal class)\n");
  Print("Derived length       : ", DerivedLength(G), "\n");
  Print("Exponent             : ", Exponent(G), "\n");
  Print("Order of stabilizer S: ", Size(S), " = 7^", Log(Size(S), 7), "\n");
  Print("Core_G(S) size       : ", Size(Core(G, S)), " (core-free)\n");

  # 2. Extremality check
  f := UltraFastF(G, S);
  Print("Fixed-point union f  : ", f, "\n");
  Print("Target f = (7^9+1)/8 : ", (7^9 + 1) / 8, "\n");
  Print("(p+1)*f = |G| + 1    : ", 8 * f = Size(G) + 1, " [8 * ", f, " = ", 8 * f, "]\n");

  # 3. Coset action and subdegrees via (S, S)-double cosets in G:
  # Each double coset D = S g S corresponds to an S-orbit of size |D|/|S| = |S : S \cap S^g|
  # in the coset space G/S, and S acts regularly on that suborbit iff S \cap S^g is normal in S.
  deg := Index(G, S);
  Print("Permutation degree   : ", deg, " = 7^", Log(deg, 7), "\n");
  Print("Action faithful      : ", Size(Core(G, S)) = 1, "\n");

  dc := DoubleCosets(G, S, S);
  subdegs := Collected(List(dc, D -> Size(D) / Size(S)));
  Print("Rank                 : ", Length(dc), "\n");
  Print("Subdegree profile    : ", subdegs, "\n");
  expected_subdegs := [ [1, 7], [7, 6], [49, 6], [343, 6], [2401, 6] ];
  Print("Matches CKNP Thm 1E  : ", subdegs = expected_subdegs, "\n");

  # 4. Suborbit regularity
  regular_ok := ForAll(dc, D -> Size(S) / Size(Intersection(S, S^Representative(D))) = Size(D) / Size(S)
                                and IsNormal(S, Intersection(S, S^Representative(D))));
  Print("Suborbits regular    : ", regular_ok, "\n");

  # 5. Normalizer chain (CKNP Theorem 2E)
  G_chain := [ S ];
  cur := S;
  for i in [1..4] do
    cur := Normalizer(G, cur);
    Add(G_chain, cur);
  od;
  Print("Normalizer chain |G_i|: ", List(G_chain, Size), "\n");
  Print("Chain indices         : ", List([1..4], i -> Index(G_chain[i+1], G_chain[i])), "\n");
  H_chain := List(G_chain, sub -> Core(sub, S));
  Print("Cores |H_i|           : ", List(H_chain, Size), "\n");
  if SHOW_TIMINGS then
    Print("Total runtime         : ", Runtime() - t_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunVerifyExtreme79();
QUIT;
