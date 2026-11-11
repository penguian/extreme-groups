# count_max_class_totals.g
# Total number of isomorphism classes of p-groups of maximal class of order p^n,
# built from ALL maximal-class parents (not only the extreme chain), and compared with:
#  (a) the SmallGroups library, where installed (ID_AVAILABLE), and
#  (b) published values: Blackburn 1958 (Sec. 4, p^4--p^5), Newman 1990 & O'Brien--Vaughan-Lee 2005
#      (99 at 5^7; Thm. 4, Tables 2--3 for p^6--p^7), and Lee--Vaughan-Lee 2024 (Thm. 1 Lie-ring
#      formula at p^8 for p >= 5, matching 7^8 = 1988 via ANUPQ and p >= 11 groups via Lazard).
#
# Usage (from repository root):
#   echo 'P_TO_RUN := 5; Read("scripts/count_max_class_totals.g");' | gap -q
#   echo 'P_TO_RUN := 7; Read("scripts/count_max_class_totals.g");' | gap -q
#
# Justification: a maximal-class group G of order p^n (n >= 4) has |Z(G)| = p, and the
# last term of its lower exponent-p central series is central and nontrivial, so it equals
# Z(G); hence G is an immediate (step size 1) descendant of G/Z(G), which has maximal
# class and order p^(n-1). Descendants are filtered by class = n - 1.

LoadPackage("anupq");
Read("lib/timings_lib.g");

if not IsBound(P_TO_RUN) then P_TO_RUN := 5; fi;
if not IsBound(N_MAX) then
  if P_TO_RUN = 7 then N_MAX := 8; else N_MAX := 7; fi;
fi;

PublishedMaxClassCount := function(p, n)
  local g;
  g := Gcd;
  if n = 4 and p > 3 then return 4; fi;
  if n = 5 and p > 3 then return 3 + 2 * g(p - 1, 3) + g(p - 1, 4); fi;
  if n = 6 and p > 5 then
    return 2 * p + 7 + 4 * g(p - 1, 3) + 4 * g(p - 1, 4) + 2 * g(p - 1, 5);
  fi;
  if n = 7 and p > 5 then
    return 2 * p^2 + 5 * p + 3 + (2 * p + 2) * g(p - 1, 3) + (p + 4) * g(p - 1, 5)
           + g(p - 1, 7) + g(p - 1, 8);
  fi;
  if n = 8 and p >= 7 then
    return 4 * p^3 + 7 * p^2 + 9 * p + 6 + (6 * p + 11) * g(p - 1, 3) + 4 * g(p - 1, 5)
           + (p + 2) * g(p - 1, 7) + (p + 3) * g(p - 1, 8) + 2 * g(p - 1, 9) + g(p - 1, 12);
  fi;
  if n = 7 and p = 5 then return 99; fi;
  return fail;
end;

RunCountMaxClassTotals := function(p, n_max)
  local t0, M, n, newM, parents_with_child, nonmax, G, D, mc, sg, pub;
  t0 := Runtime();
  Print("====================================================================\n");
  Print("TOTAL MAXIMAL-CLASS p-GROUPS, p = ", p, "\n");
  Print("====================================================================\n");
  M := [ ExtraspecialGroup(p^3, p), ExtraspecialGroup(p^3, p^2) ];
  Print("Order ", p, "^3: ", Length(M), " (two extraspecial groups)\n");
  for n in [4..n_max] do
    newM := [];
    parents_with_child := 0;
    nonmax := 0;
    for G in M do
      D := PqDescendants(G : StepSize := 1);
      mc := Filtered(D, H -> NilpotencyClassOfGroup(H) = n - 1);
      nonmax := nonmax + Length(D) - Length(mc);
      if Length(mc) > 0 then parents_with_child := parents_with_child + 1; fi;
      Append(newM, mc);
    od;
    M := newM;
    sg := "n/a";
    if ID_AVAILABLE(p^n) <> fail then
      sg := Number(AllSmallGroups(p^n), H -> NilpotencyClassOfGroup(H) = n - 1);
    fi;
    pub := PublishedMaxClassCount(p, n);
    Print("Order ", p, "^", n, ": total max-class = ", Length(M),
          " | parents with a max-class child = ", parents_with_child,
          " | non-max-class immediate descendants discarded = ", nonmax,
          " | SmallGroups = ", sg, " | published = ", pub);
    if sg <> "n/a" then
      if sg = Length(M) then Print(" | SG: PASS"); else Print(" | SG: FAIL"); fi;
    fi;
    if pub <> fail then
      if pub = Length(M) then Print(" | PUB: PASS"); else Print(" | PUB: FAIL"); fi;
    fi;
    Print("\n");
  od;
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t0, " ms\n");
  fi;
end;

RunCountMaxClassTotals(P_TO_RUN, N_MAX);
QUIT;
