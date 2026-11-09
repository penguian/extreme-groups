# classify_extreme_3_max_class.g
# Extreme 3-groups of maximal class of orders 3^3, 3^5 and 3^7.
#
# Orders 3^3 .. 3^6 are taken from the SmallGroups library. Order 3^7 is
# obtained by ANUPQ from the maximal-class groups of order 3^6 (StepSize := 1),
# as in classify_extreme_5_5_to_5_9.g and classify_extreme_7_7_and_7_9.g.
# A group G of order p^m (m = 2n-1) is extreme if some core-free subgroup S of
# order p^(n-1) has (p+1)*f(G,S) = |G|+1, where f is the size of the union of
# the conjugates of S.
#
# Validation: the step-1 ANUPQ chain from the maximal-class groups of order 3^5
# must reproduce the number of maximal-class groups of order 3^6 listed in the
# SmallGroups library.

LoadPackage("anupq");
LoadPackage("autpgrp");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

IsMaxClass := G -> NilpotencyClassOfGroup(G) = Log(Size(G), 3) - 1;

# Representatives of the isomorphism classes among a list of 3-groups.
ClassReps := function(L)
  local reps, G, H, new;
  reps := [];
  for G in L do
    new := true;
    for H in reps do
      if Size(G) = Size(H) and IsIsomorphicPGroup(G, H) then
        new := false;
        break;
      fi;
    od;
    if new then Add(reps, G); fi;
  od;
  return reps;
end;

# Extreme core-free stabilizers of G, up to conjugacy.
ExtremeStabilizers := function(G)
  local p, N, m, n, res, c, S, T;
  p := 3;
  N := Size(G);
  m := Log(N, p);
  n := (m + 1) / 2;
  res := [];
  for c in ConjugacyClassesSubgroups(G) do
    S := Representative(c);
    if Size(S) <> p^(n-1) then continue; fi;
    if Size(Core(G, S)) <> 1 then continue; fi;
    T := Union(List(RightTransversal(G, Normalizer(G, S)), g -> AsSet(S^g)));
    if (p + 1) * Length(T) = N + 1 then Add(res, S); fi;
  od;
  return res;
end;

RunClassifyExtreme3 := function()
  local m, mc, ext, i, G, mc6, mc5, from5, cand7, mc7, cent_ok, H, lcs, P1, ext7;

  Print("====================================================================\n");
  Print("EXTREME 3-GROUPS OF MAXIMAL CLASS (ORDERS 3^3, 3^5, 3^7)\n");
  Print("====================================================================\n");

  # Orders 3^3 and 3^5 from the SmallGroups library
  for m in [3, 5] do
    mc := Filtered([1..NrSmallGroups(3^m)], i -> IsMaxClass(SmallGroup(3^m, i)));
    ext := Filtered(mc, i -> Length(ExtremeStabilizers(SmallGroup(3^m, i))) > 0);
    Print("Order 3^", m, ": ", Length(mc), " maximal-class groups, ", Length(ext),
          " extreme; SmallGroup ids ", ext, "\n");
    for i in ext do
      G := SmallGroup(3^m, i);
      Print("   SmallGroup(", 3^m, ",", i, "): derived length ", DerivedLength(G),
            ", exponent ", Exponent(G), "\n");
    od;
  od;

  # Order 3^6 from the library, and validation of the ANUPQ chain from 3^5
  mc6 := List(Filtered([1..NrSmallGroups(3^6)], i -> IsMaxClass(SmallGroup(3^6, i))),
              i -> SmallGroup(3^6, i));
  mc5 := List(Filtered([1..NrSmallGroups(3^5)], i -> IsMaxClass(SmallGroup(3^5, i))),
              i -> SmallGroup(3^5, i));
  from5 := [];
  for G in mc5 do
    Append(from5, Filtered(PqDescendants(G : StepSize := 1), IsMaxClass));
  od;
  from5 := ClassReps(from5);
  Print("Order 3^6: ", Length(mc6), " maximal-class groups in SmallGroups; ",
        Length(from5), " from the ANUPQ chain starting at order 3^5\n");

  # Order 3^7 via ANUPQ from all maximal-class groups of order 3^6
  cand7 := [];
  for G in mc6 do
    Append(cand7, Filtered(PqDescendants(G : StepSize := 1), IsMaxClass));
  od;
  mc7 := ClassReps(cand7);
  Print("Order 3^7: ", Length(mc7), " maximal-class groups\n");
  cent_ok := 0;
  for H in mc7 do
    lcs := LowerCentralSeries(H);
    P1 := TwoStepCentralizer(H);
    if IsAbelian(lcs[2]) and Size(CommutatorSubgroup(P1, lcs[3])) = 1
       and Size(CommutatorSubgroup(P1, lcs[4])) = 1 then
      cent_ok := cent_ok + 1;
    fi;
  od;
  Print("Order 3^7 groups satisfying [P_2, P_2] = 1 and [P_1, P_3] = [P_1, P_4] = 1 (Theorem 9.3): ",
        cent_ok, " / ", Length(mc7), "\n");
  ext7 := Filtered(mc7, H -> Length(ExtremeStabilizers(H)) > 0);
  Print("Order 3^7: ", Length(ext7), " extreme maximal-class groups\n");
  Print("By Lemma K0 (an extreme group of order p^m has an extreme quotient of order p^(m-2)),\n");
  Print("none exists at order 3^m for any odd m >= 7 if none exists at 3^7.\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
  Print("====================================================================\n");
end;

RunClassifyExtreme3();
QUIT;
