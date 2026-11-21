# branch_depth_extreme.g
# Branch/depth audit of extreme maximal-class p-groups in the coclass tree T(p) for p = 3, 5, 7.
#
# Conventions (Dietrich 2010, J. Group Theory 13, 851-871):
#   S_n = mainline group of order p^n;
#   B_n = descendants of S_n that are not descendants of S_{n+1};
#   depth of H of order p^m in B_n is m - n.
# "Capable" here = has an immediate descendant of maximal class (class n for order p^n),
# called mc-capable. This is a refinement of ANUPQ's CapableDescendants option (p-class based);
# see the comparison printed for p = 5.

Read("lib/extreme_lib.g");
Read("lib/timings_lib.g");
RequirePackage("anupq");

# Quotient of order p^5: G / gamma_5(G).
Quot5 := function(G)
  return Image(NaturalHomomorphismByNormalSubgroup(G, LowerCentralSeries(G)[5]));
end;

# Common start: mainline up to order p^4, then split at p^5 by abelian P_1.
StartBranch4 := function(p)
  local G3, S4, d5, cap5, S5, G5, cap4Count;
  G3 := ExtraspecialGroup(p^3, p);
  cap4Count := Number(MaxClassChildren(G3, 3), IsMcCapable);
  S4 := Filtered(MaxClassChildren(G3, 3), IsMcCapable)[1];
  d5 := MaxClassChildren(S4, 4);
  cap5 := Filtered(d5, IsMcCapable);
  S5 := Filtered(cap5, P1Abelian);
  G5 := Filtered(cap5, H -> not P1Abelian(H));
  Print("p = ", p, ": order p^4 capable groups: ", cap4Count,
        "; order p^5 mc groups: ", Length(d5), ", capable: ", Length(cap5),
        ", capable with abelian P_1 (mainline S_5): ", Length(S5),
        ", capable with non-abelian P_1: ", Length(G5), "\n");
  return rec(S4 := S4, S5 := S5[1], G5 := G5, d5 := d5, cap4Count := cap4Count, cap5 := cap5);
end;

RunBranchDepthAudit := function()
  local r, E5, d6, cap6, g6, d7, ext7, ext7NonAb, d7_kids, cap7, capDescG6, lvl, kids,
        n, cand, cand_kids, cp_idx, cp, counts5, counts7, G75, G3, S4, d5, ext5;

  Print("====================================================================\n");
  Print("BRANCH AND DEPTH AUDIT OF EXTREME MAXIMAL-CLASS GROUPS (p = 3, 5, 7)\n");
  Print("====================================================================\n\n");

  # ---------------- p = 5 ----------------
  Print("--- p = 5 ---\n");
  r := StartBranch4(5);
  E5 := r.G5[1];
  d6 := MaxClassChildren(E5, 5);
  cap6 := Filtered(d6, IsMcCapable);
  Print("E5: ", Length(d6), " children at 5^6, ", Length(cap6), " capable\n");
  g6 := cap6[1];
  d7 := MaxClassChildren(g6, 6);
  ext7 := Filtered([1..Length(d7)], i -> HasTiltedExtremeStabilizer(d7[i], 5));
  ext7NonAb := Number(ext7, i -> not P1Abelian(Quot5(d7[i])));
  d7_kids := List(d7, H -> MaxClassChildren(H, 7));
  cap7 := Filtered([1..Length(d7)], i -> Length(d7_kids[i]) > 0);
  capDescG6 := Length(PqDescendants(g6 : StepSize := 1, CapableDescendants));
  Print("5^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
        ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
  Print("  extreme groups with G/gamma_5 of non-abelian P_1: ", ext7NonAb, " of ", Length(ext7), "\n");
  Print("  CapableDescendants (ANUPQ option) from g6: ", capDescG6, " vs mc-capable: ", Length(cap7), "\n");
  if r.cap4Count <> 1 or Length(r.d5) <> 9 or Length(r.cap5) <> 2 or Length(r.G5) <> 1
     or Length(d6) <> 18 or Length(cap6) <> 1
     or Length(d7) <> 70 or Length(ext7) <> 24 or ext7NonAb <> 24
     or Length(cap7) <> 1 or Length(Intersection(ext7, cap7)) <> 1 or capDescG6 <> 1 then
    Error("Branch B_4 audit mismatch for p = 5 at order <= 5^7!");
  fi;
  lvl := List(cap7, i -> d7[i]);
  kids := Concatenation(d7_kids{cap7});
  counts5 := [];
  for n in [7, 8] do
    cand := Concatenation(List(lvl, H -> MaxClassCapableChildren(H, n)));
    cand_kids := List(cand, H -> MaxClassChildren(H, n + 1));
    cp_idx := Filtered([1..Length(cand)], i -> Length(cand_kids[i]) > 0);
    cp := cand{cp_idx};
    Print("5^", n + 1, ": ", Length(kids), " groups below capable 5^", n, " groups, ", Length(cp), " capable\n");
    Add(counts5, [Length(kids), Length(cp)]);
    lvl := cp;
    kids := Concatenation(cand_kids{cp_idx});
  od;
  if counts5 <> [ [33, 0], [0, 0] ] then
    Error("Branch B_4 audit mismatch for p = 5 at orders 5^8..5^9!");
  fi;

  # ---------------- p = 7 ----------------
  Print("\n--- p = 7 ---\n");
  r := StartBranch4(7);
  G75 := r.G5[1];
  d6 := MaxClassChildren(G75, 5);
  cap6 := Filtered(d6, IsMcCapable);
  Print("G(7,5): ", Length(d6), " children at 7^6, ", Length(cap6), " capable\n");
  g6 := cap6[1];
  d7 := MaxClassChildren(g6, 6);
  ext7 := Filtered([1..Length(d7)], i -> HasTiltedExtremeStabilizer(d7[i], 7));
  ext7NonAb := Number(ext7, i -> not P1Abelian(Quot5(d7[i])));
  d7_kids := List(d7, H -> MaxClassChildren(H, 7));
  cap7 := Filtered([1..Length(d7)], i -> Length(d7_kids[i]) > 0);
  Print("7^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
        ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
  Print("  extreme groups with G/gamma_5 of non-abelian P_1: ", ext7NonAb, " of ", Length(ext7), "\n");
  if r.cap4Count <> 1 or Length(r.d5) <> 11 or Length(r.cap5) <> 2 or Length(r.G5) <> 1
     or Length(d6) <> 24 or Length(cap6) <> 1
     or Length(d7) <> 154 or Length(ext7) <> 35 or ext7NonAb <> 35
     or Length(cap7) <> 9 or Length(Intersection(ext7, cap7)) <> 5 then
    Error("Branch B_4 audit mismatch for p = 7 at order <= 7^7!");
  fi;
  lvl := List(cap7, i -> d7[i]);
  kids := Concatenation(d7_kids{cap7});
  counts7 := [];
  for n in [7, 8, 9] do
    cand := Concatenation(List(lvl, H -> MaxClassCapableChildren(H, n)));
    cand_kids := List(cand, H -> MaxClassChildren(H, n + 1));
    cp_idx := Filtered([1..Length(cand)], i -> Length(cand_kids[i]) > 0);
    cp := cand{cp_idx};
    Print("7^", n + 1, ": ", Length(kids), " groups below capable 7^", n, " groups, ", Length(cp), " capable\n");
    Add(counts7, [Length(kids), Length(cp)]);
    lvl := cp;
    kids := Concatenation(cand_kids{cp_idx});
  od;
  if counts7 <> [ [1557, 29], [12207, 20], [22459, 0] ] then
    Error("Branch B_4 audit mismatch for p = 7 at orders 7^8..7^10!");
  fi;

  # ---------------- p = 3 ----------------
  Print("\n--- p = 3 (outside the p >= 5 argument; shown for completeness) ---\n");
  G3 := ExtraspecialGroup(27, 3);
  S4 := Filtered(MaxClassChildren(G3, 3), IsMcCapable);
  Print("3^4 capable groups: ", Length(S4), "\n");
  d5 := MaxClassChildren(S4[1], 4);
  ext5 := Filtered(d5, H -> HasTiltedExtremeStabilizer(H, 3));
  Print("3^5: ", Length(d5), " groups, ", Length(ext5), " extreme, of which capable: ",
        Number(ext5, IsMcCapable), "\n");
  if Length(S4) <> 1 or Length(d5) <> 6 or Length(ext5) <> 3 or Number(ext5, IsMcCapable) <> 0 then
    Error("Branch B_4 audit mismatch for p = 3!");
  fi;
  PrintTimingIfEnabled();
  Print("====================================================================\n");
end;

RunBranchDepthAudit();
QUIT;
