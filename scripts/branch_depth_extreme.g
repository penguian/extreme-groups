# branch_depth_extreme.g
# Branch/depth audit of extreme maximal-class p-groups in the coclass tree T(p), p = 3, 5, 7
# (Proposition 8.4 and Table 3).
#
# Conventions (Dietrich 2010, J. Group Theory 13, 851-871):
#   S_n = mainline group of order p^n;
#   B_n = descendants of S_n that are not descendants of S_{n+1};
#   depth of H of order p^m in B_n is m - n.
# "Capable" here = has an immediate descendant of maximal class (class n for order p^n),
# called mc-capable. This is a refinement of ANUPQ's CapableDescendants option (p-class based);
# see the comparison printed for p = 5.

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

# Maximal-class immediate descendants of G (|G| = p^n).
McChildren := function(G, n)
  return Filtered(PqDescendants(G : StepSize := 1), H -> NilpotencyClassOfGroup(H) = n);
end;

# Every mc-capable child K of G (having a step-1 child M of nilpotency class n+1)
# also has p-class(M) = n+1 since gamma_{n+1}(M) <= P_{n+1}(M), so K appears in
# PqDescendants(G : StepSize := 1, CapableDescendants).
McCapableChildren := function(G, n)
  return Filtered(PqDescendants(G : StepSize := 1, CapableDescendants),
                  H -> NilpotencyClassOfGroup(H) = n);
end;

IsMcCapable := G -> Length(McChildren(G, LogInt(Size(G), PrimeDivisors(Size(G))[1]))) > 0;

# Quotient of order p^5: G / gamma_5(G).
Quot5 := function(G)
  return Image(NaturalHomomorphismByNormalSubgroup(G, LowerCentralSeries(G)[5]));
end;

# Extremality test: some core-free S of order p^(n-1), S = <x_4, x_2 * x_3^k> (k = 0..p-1),
# with (p+1)*f(G, S) = |G| + 1. For p = 3 (order 3^5), a full search over subgroup classes is used.
IsExtremeGen := function(G, p)
  local x, m, n, S, k, c;
  m := LogInt(Size(G), p);
  n := (m + 1) / 2;
  if p = 3 then
    for c in ConjugacyClassesSubgroups(G) do
      S := Representative(c);
      if Size(S) = p^(n-1) and Size(Core(G, S)) = 1
         and UltraFastF(G, S) = (p^m + 1) / (p + 1) then
        return true;
      fi;
    od;
    return false;
  fi;
  x := Pcgs(G);
  for k in [0..p-1] do
    S := Subgroup(G, [x[4], x[2] * x[3]^k]);
    if Size(S) = p^(n-1) and not (x[m] in S) and UltraFastF(G, S) = (p^m + 1) / (p + 1) then
      return true;
    fi;
  od;
  return false;
end;

# Common start: mainline up to order p^4, then split at p^5 by abelian P_1.
Start := function(p)
  local G3, S4, d5, cap5, S5, G5;
  G3 := ExtraspecialGroup(p^3, p);
  S4 := Filtered(McChildren(G3, 3), H -> IsMcCapable(H))[1];
  d5 := McChildren(S4, 4);
  cap5 := Filtered(d5, IsMcCapable);
  S5 := Filtered(cap5, P1Abelian);
  G5 := Filtered(cap5, H -> not P1Abelian(H));
  Print("p = ", p, ": order p^4 capable groups: ", Number(McChildren(G3, 3), IsMcCapable),
        "; order p^5 mc groups: ", Length(d5), ", capable: ", Length(cap5),
        ", capable with abelian P_1 (mainline S_5): ", Length(S5),
        ", capable with non-abelian P_1: ", Length(G5), "\n");
  return rec(S4 := S4, S5 := S5[1], G5 := G5, d5 := d5);
end;

RunBranchDepthAudit := function()
  local r, E5, d6, cap6, g6, d7, ext7, d7_kids, cap7, lvl, kids,
        n, cand, cand_kids, cp_idx, cp, G75, G3, S4, d5, ext5;

  Print("====================================================================\n");
  Print("BRANCH AND DEPTH AUDIT OF EXTREME MAXIMAL-CLASS GROUPS (p = 3, 5, 7)\n");
  Print("====================================================================\n\n");

  # ---------------- p = 5 ----------------
  Print("--- p = 5 ---\n");
  r := Start(5);
  E5 := r.G5[1];
  d6 := McChildren(E5, 5);
  cap6 := Filtered(d6, IsMcCapable);
  Print("E5: ", Length(d6), " children at 5^6, ", Length(cap6), " capable\n");
  g6 := cap6[1];
  d7 := McChildren(g6, 6);
  ext7 := Filtered([1..Length(d7)], i -> IsExtremeGen(d7[i], 5));
  d7_kids := List(d7, H -> McChildren(H, 7));
  cap7 := Filtered([1..Length(d7)], i -> Length(d7_kids[i]) > 0);
  Print("5^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
        ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
  Print("  extreme groups with G/gamma_5 of non-abelian P_1: ",
        Number(ext7, i -> not P1Abelian(Quot5(d7[i]))), " of ", Length(ext7), "\n");
  Print("  CapableDescendants (ANUPQ option) from g6: ",
        Length(PqDescendants(g6 : StepSize := 1, CapableDescendants)),
        " vs mc-capable: ", Length(cap7), "\n");
  lvl := List(cap7, i -> d7[i]);
  kids := Concatenation(d7_kids{cap7});
  for n in [7, 8] do
    cand := Concatenation(List(lvl, H -> McCapableChildren(H, n)));
    cand_kids := List(cand, H -> McChildren(H, n + 1));
    cp_idx := Filtered([1..Length(cand)], i -> Length(cand_kids[i]) > 0);
    cp := cand{cp_idx};
    Print("5^", n + 1, ": ", Length(kids), " groups below capable 5^", n, " groups, ", Length(cp), " capable\n");
    lvl := cp;
    kids := Concatenation(cand_kids{cp_idx});
  od;

  # ---------------- p = 7 ----------------
  Print("\n--- p = 7 ---\n");
  r := Start(7);
  G75 := r.G5[1];
  d6 := McChildren(G75, 5);
  cap6 := Filtered(d6, IsMcCapable);
  Print("G(7,5): ", Length(d6), " children at 7^6, ", Length(cap6), " capable\n");
  g6 := cap6[1];
  d7 := McChildren(g6, 6);
  ext7 := Filtered([1..Length(d7)], i -> IsExtremeGen(d7[i], 7));
  d7_kids := List(d7, H -> McChildren(H, 7));
  cap7 := Filtered([1..Length(d7)], i -> Length(d7_kids[i]) > 0);
  Print("7^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
        ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
  Print("  extreme groups with G/gamma_5 of non-abelian P_1: ",
        Number(ext7, i -> not P1Abelian(Quot5(d7[i]))), " of ", Length(ext7), "\n");
  lvl := List(cap7, i -> d7[i]);
  kids := Concatenation(d7_kids{cap7});
  for n in [7, 8, 9] do
    cand := Concatenation(List(lvl, H -> McCapableChildren(H, n)));
    cand_kids := List(cand, H -> McChildren(H, n + 1));
    cp_idx := Filtered([1..Length(cand)], i -> Length(cand_kids[i]) > 0);
    cp := cand{cp_idx};
    Print("7^", n + 1, ": ", Length(kids), " groups below capable 7^", n, " groups, ", Length(cp), " capable\n");
    lvl := cp;
    kids := Concatenation(cand_kids{cp_idx});
  od;

  # ---------------- p = 3 ----------------
  Print("\n--- p = 3 (outside the p >= 5 argument; shown for completeness) ---\n");
  G3 := ExtraspecialGroup(27, 3);
  S4 := Filtered(McChildren(G3, 3), IsMcCapable);
  Print("3^4 capable groups: ", Length(S4), "\n");
  d5 := McChildren(S4[1], 4);
  ext5 := Filtered(d5, H -> IsExtremeGen(H, 3));
  Print("3^5: ", Length(d5), " groups, ", Length(ext5), " extreme, of which capable: ",
        Number(ext5, IsMcCapable), "\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunBranchDepthAudit();
QUIT;
