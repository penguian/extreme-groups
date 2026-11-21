# verify_extreme_7_9.g
# Self-contained verification of an extreme transitive 7-group of maximal class of order 7^9.
# Group lineage: G(7,5) -> g1 (order 7^6) -> d7[15] (order 7^7) -> Child 13 (order 7^8) -> Group 1 (order 7^9).
# Stabilizer: S = <x4, x2*x3> of order 7^4 = 2401, Core_G(S) = 1.
# Degree: d = [G:S] = 7^5 = 16807.
# Extremality: (p+1)*f(G,S) = |G| + 1 <=> 8 * 5044201 = 40353608.

Read("lib/klg_lib.g");
Read("lib/timings_lib.g");
RequirePackage("anupq");

RunVerifyExtreme79 := function()
  local G75, des75_1, g1, des_g1, G15, des8, c13, des9, G,
        x, S, f, target_f, deg, dc, subdegs, expected_subdegs, regular_ok,
        tower, chain_sizes, chain_indices, core_sizes;

  # 1. Construct root G(7,5) on a weighted ANUPQ p-quotient presentation and advance down the tree.
  G75 := PqWeightedPresentation(KLGpc(7, 5), 7);
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
  target_f := ExtremeTargetF(7, 9);
  Print("Fixed-point union f  : ", f, "\n");
  Print("Target f = (7^9+1)/8 : ", target_f, "\n");
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
  Print("Matches CKNP profile : ", subdegs = expected_subdegs, "\n");

  # 4. Suborbit regularity
  regular_ok := ForAll(dc, D -> Size(S) / Size(Intersection(S, S^Representative(D))) = Size(D) / Size(S)
                                and IsNormal(S, Intersection(S, S^Representative(D))));
  Print("Suborbits regular    : ", regular_ok, "\n");

  # 5. Normalizer-core tower
  tower := NormalizerCoreTower(G, S);
  chain_sizes := List(tower.asc, Size);
  chain_indices := List([1..Length(tower.asc)-1], i -> Index(tower.asc[i+1], tower.asc[i]));
  core_sizes := List(tower.coresAsc, Size);
  Print("Normalizer chain |G_i|: ", chain_sizes, "\n");
  Print("Chain indices         : ", chain_indices, "\n");
  Print("Cores |H_i|           : ", core_sizes, "\n");

  if Size(G) <> 7^9 or NilpotencyClassOfGroup(G) <> 8 or DerivedLength(G) <> 3
     or Exponent(G) <> 49 or Size(S) <> 7^4 or Size(Core(G, S)) <> 1
     or f <> target_f or deg <> 7^5 or subdegs <> expected_subdegs or not regular_ok
     or chain_sizes <> [ 2401, 16807, 117649, 823543, 5764801, 40353607 ]
     or chain_indices <> [ 7, 7, 7, 7, 7 ]
     or core_sizes <> [ 2401, 2401, 343, 49, 7, 1 ] then
    Error("Order-7^9 extreme group verification failed!");
  fi;
  PrintTimingIfEnabled();
  Print("====================================================================\n");
end;

RunVerifyExtreme79();
QUIT;
