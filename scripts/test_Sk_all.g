# test_Sk_all.g
# For ALL 625 consistent parameter tuples alpha, verify Lemma 6.1 and Theorem 6.2:
#  (1) [x_4, x_2 * x_3^k] = x_6 * x_7^(alpha_2 + k * alpha_4),
#  (2) (x_2 * x_3^k)^5 = x_6^4 * x_7^(alpha_6 - k),
#  (3) for alpha_3 <> 0, k_0 = (alpha_2 + alpha_6) / alpha_3 mod 5 gives
#      |<x_4, x_2 * x_3^{k_0}>| = 125, and for all other k the order is 625.

Read("lib/alpha_lib.g");
Read("lib/timings_lib.g");

RunTestSkAll := function()
  local alphas, bad1, bad2, bad3, n3, mism, a, G, gg, pcgs, k, s1, s2, e1, e2, k0, sz;
  alphas := ConsistentAlphas();
  Print("number of consistent alphas: ", Length(alphas), "\n");
  bad1 := 0; bad2 := 0; bad3 := 0; n3 := 0; mism := [];
  for a in alphas do
    G := DescGroup(a);
    gg := GeneratorsOfGroup(G);
    pcgs := Pcgs(G);
    for k in [0..4] do
      s1 := gg[2] * gg[3]^k;
      s2 := gg[4];
      e1 := ExponentsOfPcElement(pcgs, Comm(s2, s1));
      e2 := ExponentsOfPcElement(pcgs, s1^5);
      if e1 <> [0, 0, 0, 0, 0, 1, (a[2] + k * a[4]) mod 5] then bad1 := bad1 + 1; fi;
      if e2 <> [0, 0, 0, 0, 0, 4, (a[6] - k) mod 5] then bad2 := bad2 + 1; fi;
    od;
    if a[3] <> 0 then
      n3 := n3 + 1;
      k0 := ((a[2] + a[6]) * (1 / a[3] mod 5)) mod 5;
      for k in [0..4] do
        sz := Size(Subgroup(G, [gg[2] * gg[3]^k, gg[4]]));
        if (k = k0 and sz <> 125) or (k <> k0 and sz <> 625) then
          bad3 := bad3 + 1;
          Add(mism, [a, k, sz]);
        fi;
      od;
    fi;
  od;
  Print("violations of (1): ", bad1, ", of (2): ", bad2, ", of (3): ", bad3,
        " over ", n3, " alphas with a3<>0\n");
  Print("mismatches: ", Length(mism), "\n");
  if Length(mism) > 0 then
    Print(mism{[1..Minimum(5, Length(mism))]}, "\n");
  fi;
  Print("finished\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunTestSkAll();
QUIT;
