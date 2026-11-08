# classify_extreme_7_7_and_7_9.g
# Complete enumeration and classification of extreme 7-groups of maximal class
# of orders 7^5, 7^7, and 7^9 (Theorem 8.7 and Table 2).

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

# Given the polycyclic generating sequence x = Pcgs(G9) of a maximal-class group G9
# of order 7^9 in one of the surviving sectors (where c_{6,2} - c_{6,3} - mu_3 * c_{7,2} <> 0 mod 7),
# return the unique parameter k_0 in {0..6} from Theorem 8.7 for which
#   (c_{6,2} - c_{6,3} - mu_3 * c_{7,2}) * k_0 === c_{6,2} * alpha_6 + beta + alpha_2 * c_{7,2} (mod 7),
# ensuring that S = <x_4, x_2 * x_3^{k_0}> has order 7^4 = 2401.
UniqueStabilizerParam79 := function(x)
  local alpha6, alpha2, mu3, e62, c62, beta, c63, c72, lhs_coeff, rhs_val;
  alpha6 := ExponentsOfPcElement(x, x[2]^7)[9];
  alpha2 := ExponentsOfPcElement(x, Comm(x[4], x[2]))[7];
  mu3 := ExponentsOfPcElement(x, Comm(x[4], x[3]))[7];
  e62 := ExponentsOfPcElement(x, Comm(x[6], x[2]));
  c62 := e62[8];
  beta := e62[9];
  c63 := ExponentsOfPcElement(x, Comm(x[6], x[3]))[9];
  c72 := ExponentsOfPcElement(x, Comm(x[7], x[2]))[9];
  lhs_coeff := (c62 - c63 - mu3 * c72) mod 7;
  rhs_val := (c62 * alpha6 + beta + alpha2 * c72) mod 7;
  return (rhs_val * PowerModInt(lhs_coeff, 5, 7)) mod 7;
end;

RunClassifyExtreme7 := function()
  local t_start, G3, d4_all, d4_cap, d5_all, d5_cap, g5, d6_all, d6_cap, g6,
        d7, target_f7, ext7, idx7, G7, x, S7, cap7_indices, cap8_by_idx7,
        c8, c8_cap, mu3, c52, surviving_cap7, target_f9, total_7_9,
        total_ext_7_9, cap8, G8, d9, branch_ok, dl_list, exp_list, idx9,
        G9, k0, S, cur, ok, j, G9_1, x1, k0_1, f_val;

  t_start := Runtime();

  Print("====================================================================\n");
  Print("CLASSIFICATION OF EXTREME 7-GROUPS OF MAXIMAL CLASS (ORDERS 7^5..7^9)\n");
  Print("====================================================================\n");

  G3 := ExtraspecialGroup(7^3, 7);
  d4_all := PqDescendants(G3 : StepSize := 1);
  d4_cap := PqDescendants(G3 : StepSize := 1, CapableDescendants);
  Print("Order 7^4: ", Length(d4_all), " maximal-class groups (", Length(d4_cap), " capable)\n");

  d5_all := PqDescendants(d4_cap[1] : StepSize := 1);
  d5_cap := PqDescendants(d4_cap[1] : StepSize := 1, CapableDescendants);
  Print("Order 7^5: ", Length(d5_all), " maximal-class groups (", Length(d5_cap), " capable)\n");

  # g5 = d5_cap[2] is G(7, 5) with [x_3, x_2] = x_5
  g5 := d5_cap[2];
  d6_all := PqDescendants(g5 : StepSize := 1);
  d6_cap := PqDescendants(g5 : StepSize := 1, CapableDescendants);
  Print("Order 7^6 (from G(7,5)): ", Length(d6_all), " descendants (", Length(d6_cap), " capable)\n");

  g6 := d6_cap[1];
  d7 := PqDescendants(g6 : StepSize := 1);
  Print("Order 7^7 (from g6): ", Length(d7), " descendants\n");

  # Classify all 154 groups in d7 at order 7^7
  target_f7 := (7^7 + 1) / 8;
  ext7 := [];
  for idx7 in [1..Length(d7)] do
    G7 := d7[idx7];
    x := Pcgs(G7);
    if IsOne(Comm(x[4], x[3])) or IsOne(Comm(x[5], x[2])) then
      continue;
    fi;
    # Check x_2^7 = 1 (exponent of P_1 is 7) and S_0 = <x_4, x_2, [x_4, x_2]>
    S7 := Subgroup(G7, [x[4], x[2]]);
    if Size(S7) = 343 and not (x[7] in S7) then
      if UltraFastF(G7, S7) = target_f7 then
        Add(ext7, idx7);
      fi;
    fi;
  od;
  Print("Order 7^7 extreme groups: ", Length(ext7), " classes -> ", ext7, "\n\n");

  # Audit all 9 capable groups in d7 and identify those that are both extreme at 7^7
  # and have capable descendants at 7^8.
  cap7_indices := [];
  cap8_by_idx7 := [];
  for idx7 in [1..Length(d7)] do
    c8 := PqDescendants(d7[idx7] : StepSize := 1);
    if Length(c8) > 0 then
      Add(cap7_indices, idx7);
      c8_cap := PqDescendants(d7[idx7] : StepSize := 1, CapableDescendants);
      cap8_by_idx7[idx7] := c8_cap;
      x := Pcgs(d7[idx7]);
      mu3 := ExponentsOfPcElement(x, Comm(x[4], x[3]))[7];
      c52 := ExponentsOfPcElement(x, Comm(x[5], x[2]))[7];
      Print("Capable d7[", idx7, "]: mu3=", mu3, ", c52=", c52,
            ", |d8|=", Length(c8), ", |cap8|=", Length(c8_cap), "\n");
    fi;
  od;

  # Among the 5 capable extreme groups at 7^7 ([85, 99, 113, 127, 141], mu_3 in {6,5,4,3,2}):
  # - d7[99] (mu_3 = 5 === -2 mod 7) has |cap8| = 0 (weight-9 Jacobi pole 2*lambda + mu_3 = 0);
  # - d7[85] (mu_3 = 6 === -1 mod 7) has c_{7,2} = 0 at 7^9 (killed by Lemma 8.3);
  # leaving the 3 surviving branches [113, 127, 141] (mu_3 in {4, 3, 2} mod 7).
  surviving_cap7 := Filtered(Intersection(ext7, cap7_indices),
    i -> Length(cap8_by_idx7[i]) > 0 and
         ExponentsOfPcElement(Pcgs(d7[i]), Comm(Pcgs(d7[i])[4], Pcgs(d7[i])[3]))[7] in [2, 3, 4]);
  if surviving_cap7 <> [113, 127, 141] then
    Error("Unexpected surviving capable extreme 7^7 indices: ", surviving_cap7);
  fi;

  Print("\n--- Order 7^9 classification across surviving capable groups d7[113], d7[127], d7[141] ---\n");
  target_f9 := (7^9 + 1) / 8;
  total_7_9 := 0;
  total_ext_7_9 := 0;

  for idx7 in surviving_cap7 do
    cap8 := cap8_by_idx7[idx7];
    for c8 in [1..Length(cap8)] do
      G8 := cap8[c8];
      d9 := PqDescendants(G8 : StepSize := 1);
      branch_ok := 0;
      dl_list := [];
      exp_list := [];
      for idx9 in [1..Length(d9)] do
        G9 := d9[idx9];
        total_7_9 := total_7_9 + 1;
        x := Pcgs(G9);
        mu3 := ExponentsOfPcElement(x, Comm(x[4], x[3]))[7];
        k0 := UniqueStabilizerParam79(x);

        S := Subgroup(G9, [x[4], x[2] * x[3]^k0]);
        if Size(S) = 2401 and not (x[9] in S) then
          # Since Z(G9) = <x[9]> is the unique minimal normal subgroup of G9,
          # not (x[9] in S) already implies Core(G9, S) = 1.
          # At j = 1, S is normal in cur = Normalizer(G9, S), so Core(cur, S) = S.
          cur := Normalizer(G9, S);
          ok := (Size(cur) = 7^5);
          for j in [2..4] do
            if not ok then break; fi;
            cur := Normalizer(G9, cur);
            if Size(cur) <> 7^(4+j) or Size(Core(cur, S)) <> 7^(5-j) then
              ok := false;
              break;
            fi;
          od;
          if ok then
            branch_ok := branch_ok + 1;
            total_ext_7_9 := total_ext_7_9 + 1;
            Add(dl_list, DerivedLength(G9));
            Add(exp_list, Exponent(G9));
          fi;
        fi;
      od;

      # Direct check of f(G, S) = target_f9 on the first group of the branch
      G9_1 := d9[1];
      x1 := Pcgs(G9_1);
      k0_1 := UniqueStabilizerParam79(x1);
      f_val := UltraFastF(G9_1, Subgroup(G9_1, [x1[4], x1[2] * x1[3]^k0_1]));

      Print("Branch d7[", idx7, "] (mu3=", mu3, ") -> cap8[", c8, "]: ",
            branch_ok, " / ", Length(d9), " extreme | ",
            "f(d9[1])=", f_val, " | DL=", Collected(dl_list),
            " | Exp=", Collected(exp_list), "\n");
    od;
  od;

  Print("====================================================================\n");
  Print("TOTAL SURVIVING 7^9 GROUPS : ", total_7_9, "\n");
  Print("TOTAL EXTREME 7^9 GROUPS   : ", total_ext_7_9, "\n");
  if SHOW_TIMINGS then
    Print("Total runtime              : ", Runtime() - t_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunClassifyExtreme7();
QUIT;
