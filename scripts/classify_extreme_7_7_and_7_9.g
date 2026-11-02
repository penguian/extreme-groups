# classify_extreme_7_7_and_7_9.g
# Complete enumeration and classification of extreme 7-groups of maximal class
# of orders 7^5, 7^7, and 7^9.

LoadPackage("anupq");

UltraFastF := function(G, H)
  local reps, ccs;
  reps := List(ConjugacyClasses(H), Representative);
  ccs := Set(List(reps, r -> ConjugacyClass(G, r)));
  return Sum(ccs, Size);
end;

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

# g5 = d5_cap[2] is G(7,5) with [x3,x2] = x5
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
  # Check x2^7 = 1 (exponent of P_1 is 7) and S_0 = <x4, x2, [x4,x2]>
  S7 := Subgroup(G7, [x[4], x[2]]);
  if Size(S7) = 343 and not (x[7] in S7) then
    if UltraFastF(G7, S7) = target_f7 then
      Add(ext7, idx7);
    fi;
  fi;
od;
Print("Order 7^7 extreme groups: ", Length(ext7), " classes -> ", ext7, "\n\n");

# Now audit all 9 capable groups in d7 and classify order 7^9
cap7_indices := [];
for idx7 in [1..Length(d7)] do
  c8 := PqDescendants(d7[idx7] : StepSize := 1);
  if Length(c8) > 0 then
    Add(cap7_indices, idx7);
    c8_cap := PqDescendants(d7[idx7] : StepSize := 1, CapableDescendants);
    x := Pcgs(d7[idx7]);
    mu3 := ExponentsOfPcElement(x, Comm(x[4], x[3]))[7];
    c52 := ExponentsOfPcElement(x, Comm(x[5], x[2]))[7];
    Print("Capable d7[", idx7, "]: mu3=", mu3, ", c52=", c52,
          ", |d8|=", Length(c8), ", |cap8|=", Length(c8_cap), "\n");
  fi;
od;

Print("\n--- Order 7^9 classification across surviving capable groups d7[113], d7[127], d7[141] ---\n");
target_f9 := (7^9 + 1) / 8;
total_7_9 := 0;
total_ext_7_9 := 0;

for idx7 in [113, 127, 141] do
  cap8 := PqDescendants(d7[idx7] : StepSize := 1, CapableDescendants);
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
      k0 := (rhs_val * PowerModInt(lhs_coeff, 5, 7)) mod 7;

      S := Subgroup(G9, [x[4], x[2]*x[3]^k0]);
      if Size(S) = 2401 and not (x[9] in S) then
        cur := S;
        ok := true;
        for j in [1..4] do
          cur := Normalizer(G9, cur);
          if Size(cur) <> 7^(4+j) or Size(Core(cur, S)) <> 7^(5-j) then
            ok := false;
            break;
          fi;
        od;
        if ok and Size(Core(G9, S)) = 1 then
          branch_ok := branch_ok + 1;
          total_ext_7_9 := total_ext_7_9 + 1;
          Add(dl_list, DerivedLength(G9));
          Add(exp_list, Exponent(G9));
        fi;
      fi;
    od;
    # Also run direct UltraFastF on first group of branch
    G9_1 := d9[1];
    x1 := Pcgs(G9_1);
    alpha6 := ExponentsOfPcElement(x1, x1[2]^7)[9];
    alpha2 := ExponentsOfPcElement(x1, Comm(x1[4], x1[2]))[7];
    mu3 := ExponentsOfPcElement(x1, Comm(x1[4], x1[3]))[7];
    e62 := ExponentsOfPcElement(x1, Comm(x1[6], x1[2]));
    c62 := e62[8]; beta := e62[9];
    c63 := ExponentsOfPcElement(x1, Comm(x1[6], x1[3]))[9];
    c72 := ExponentsOfPcElement(x1, Comm(x1[7], x1[2]))[9];
    k0_1 := (((c62 * alpha6 + beta + alpha2 * c72) mod 7) * PowerModInt((c62 - c63 - mu3 * c72) mod 7, 5, 7)) mod 7;
    f_val := UltraFastF(G9_1, Subgroup(G9_1, [x1[4], x1[2]*x1[3]^k0_1]));

    Print("Branch d7[", idx7, "] (mu3=", mu3, ") -> cap8[", c8, "]: ",
          branch_ok, " / ", Length(d9), " extreme | ",
          "f(d9[1])=", f_val, " | DL=", Collected(dl_list),
          " | Exp=", Collected(exp_list), "\n");
  od;
od;

Print("====================================================================\n");
Print("TOTAL SURVIVING 7^9 GROUPS : ", total_7_9, "\n");
Print("TOTAL EXTREME 7^9 GROUPS   : ", total_ext_7_9, "\n");
Print("Total runtime              : ", Runtime() - t_start, " ms\n");
Print("====================================================================\n");
QUIT;
