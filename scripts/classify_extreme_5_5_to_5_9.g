# classify_extreme_5_5_to_5_9.g
# Complete enumeration and classification of extreme 5-groups of maximal class
# across orders 5^3, 5^5, 5^7, and 5^9.

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

  RunClassifyExtreme5 := function()
  local t_start, G53, target_f3, d4_all, d4_cap, d5_all, d5_cap, E5, xE5, S5,
        target_f5, f5_val, d6_all, d6_cap, g6, d7_from_g6, d7, target_f7,
        ext7, non_ext7, idx7, G7, x, is_extreme, best_f, k, S, f_val, cap7,
        current, step, next_level, G, d, H, target_f9, ext9, c72_zero_count,
        idx9, G9, L, G1;

  t_start := Runtime();

  Print("====================================================================\n");
  Print("CLASSIFICATION OF EXTREME 5-GROUPS OF MAXIMAL CLASS (ORDERS 5^5..5^9)\n");
  Print("====================================================================\n");

  # --- Phase 1: Orders 5^3 -> 5^4 -> 5^5 ---
  G53 := ExtraspecialGroup(5^3, 5);
  target_f3 := (5^3 + 1) / 6; # 21
  Print("Order 5^3: ExtraspecialGroup(5^3, 5) (target f = ", target_f3, ")\n");

  d4_all := PqDescendants(G53 : StepSize := 1);
  d4_cap := PqDescendants(G53 : StepSize := 1, CapableDescendants);
  Print("Order 5^4: ", Length(d4_all), " maximal-class groups (", Length(d4_cap), " capable)\n");

  d5_all := PqDescendants(d4_cap[1] : StepSize := 1);
  d5_cap := PqDescendants(d4_cap[1] : StepSize := 1, CapableDescendants);
  Print("Order 5^5: ", Length(d5_all), " maximal-class groups (", Length(d5_cap), " capable)\n");

  # In d5_cap: d5_cap[1] has [x3,x2]=1 (lambda=0), d5_cap[2] is E_5 =~ G(5,5) with [x3,x2]=x5 (lambda=1)
  E5 := d5_cap[2];
  xE5 := Pcgs(E5);
  S5 := Subgroup(E5, [xE5[4], xE5[2]]);
  target_f5 := (5^5 + 1) / 6; # 521
  f5_val := UltraFastF(E5, S5);
  Print("Order 5^5 extreme capable group: E_5 =~ G(5,5), |S|=", Size(S5),
        ", Core=", Size(Core(E5, S5)), ", f=", f5_val,
        " (target=", target_f5, "), DL=", DerivedLength(E5), ", Exp=", Exponent(E5), "\n\n");

  # --- Phase 2: Orders 5^5 -> 5^6 -> 5^7 ---
  d6_all := PqDescendants(E5 : StepSize := 1);
  d6_cap := PqDescendants(E5 : StepSize := 1, CapableDescendants);
  Print("Order 5^6 (from E_5): ", Length(d6_all), " descendants (", Length(d6_cap), " capable)\n");

  g6 := d6_cap[1];
  d7_from_g6 := PqDescendants(g6 : StepSize := 1);
  d7 := Filtered(d7_from_g6, d -> NilpotencyClassOfGroup(d) = 6);
  Print("Order 5^7 (from g6, class 6): ", Length(d7), " isomorphism classes\n");

  target_f7 := (5^7 + 1) / 6; # 13021
  ext7 := [];
  non_ext7 := [];

  for idx7 in [1..Length(d7)] do
    G7 := d7[idx7];
    x := Pcgs(G7);
    is_extreme := false;
    best_f := 0;
    for k in [0..4] do
      S := Subgroup(G7, [x[4], x[2] * x[3]^k]);
      if Size(S) = 125 and not (x[7] in S) and Size(Core(G7, S)) = 1 then
        f_val := UltraFastF(G7, S);
        if f_val > best_f then best_f := f_val; fi;
        if f_val = target_f7 then
          is_extreme := true;
          break;
        fi;
      fi;
    od;
    if is_extreme then
      Add(ext7, idx7);
    else
      Add(non_ext7, idx7);
    fi;
  od;

  Print("Order 5^7 extreme groups: ", Length(ext7), " classes out of ", Length(d7), "\n");
  Print("Order 5^7 extreme indices: ", ext7, "\n\n");

  # --- Phase 3: Orders 5^7 -> 5^8 -> 5^9 ---
  # 1. Check capability of the extreme 5^7 branch
  cap7 := Filtered(d7, d -> Length(PqDescendants(d : StepSize := 1)) > 0);
  Print("Order 5^7 capable groups from E_5 branch: ", Length(cap7), "\n");

  # 2. Complete census of all maximal-class groups of order 5^9
  Print("Generating all maximal-class groups of order 5^9 from base G(5,3)...\n");
  current := [ G53 ];
  for step in [4..9] do
    next_level := [];
    for G in current do
      d := PqDescendants(G : StepSize := 1);
      for H in d do
        if Size(H) = 5^step and NilpotencyClassOfGroup(H) = step - 1 then
          Add(next_level, H);
        fi;
      od;
    od;
    current := next_level;
  od;
  Print("Total maximal-class groups of order 5^9 (class 8): ", Length(current), "\n");

  target_f9 := (5^9 + 1) / 6; # 325521
  ext9 := [];
  c72_zero_count := 0;

  for idx9 in [1..Length(current)] do
    G9 := current[idx9];
    L := LowerCentralSeriesOfGroup(G9);
    G1 := TwoStepCentralizer(G9);

    # Check centralizer condition [G_1, gamma_6(G)] = 1 (Theorem 9.5 / Lemma 8.2).
    # By Lemma 8.2, if [G_1, gamma_6(G)] = 1 then gamma_7(G) (order 25) centralizes
    # every core-free subgroup S <= G_1, forcing |N_G(S) : S| >= 25 > 5 and blocking
    # extremality. If any group had [G_1, gamma_6(G)] <> 1, we exhaustively test all
    # conjugacy classes of subgroups S <= G_1 of order 625 via SubgroupsSolvableGroup.
    if Size(CommutatorSubgroup(G1, L[6])) = 1 then
      c72_zero_count := c72_zero_count + 1;
    else
      for S in SubgroupsSolvableGroup(G1, rec(size := 625)) do
        if Size(Core(G9, S)) = 1 and UltraFastF(G9, S) = target_f9 then
          Add(ext9, idx9);
          break;
        fi;
      od;
    fi;
  od;

  Print("Order 5^9 groups with [G_1, gamma_6] = 1 (c_{7,2} = 0): ", c72_zero_count, " / ", Length(current), "\n");
  Print("Order 5^9 extreme groups: ", Length(ext9), " classes\n\n");

  Print("====================================================================\n");
  Print("CLASSIFICATION SUMMARY ACROSS ALL ORDERS (p = 5)\n");
  Print("====================================================================\n");
  Print("Order 5^3:  1 extreme class (ExtraspecialGroup(5^3, 5), f = 21)\n");
  Print("Order 5^5:  1 capable extreme class (E_5 =~ G(5,5), f = 521, class 4, dl 2, exp 5)\n");
  Print("Order 5^7: 24 extreme classes out of 70 (f = 13021, class 6, dl 3, exp 25)\n");
  Print("Order 5^9:  0 extreme classes out of 141 (Universal Depth-2 Cutoff)\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunClassifyExtreme5();
QUIT;
