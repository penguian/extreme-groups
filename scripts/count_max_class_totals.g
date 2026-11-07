# count_max_class_totals.g
# Total number of isomorphism classes of p-groups of maximal class of order p^n,
# built from ALL maximal-class parents (not only the extreme chain), and compared with
#  (a) the SmallGroups library, where installed (ID_AVAILABLE), and
#  (b) published values: O Brien--Vaughan-Lee 2005 (99 at 5^7), Lee--Vaughan-Lee Thm 4.
# Usage (from repository root):
#   echo "P_TO_RUN := 5; Read(\"scripts/count_max_class_totals.g\");" | gap -q
# Justification: a maximal-class group G of order p^n (n>=4) has |Z(G)| = p, and the
# last term of its lower exponent-p central series is central and nontrivial, so it equals
# Z(G); hence G is an immediate (step size 1) descendant of G/Z(G), which has maximal
# class and order p^(n-1).  Descendants are filtered by class = n-1.
LoadPackage("anupq");
if not IsBound(P_TO_RUN) then P_TO_RUN := 5; fi;
if not IsBound(N_MAX) then N_MAX := 7; fi;
p := P_TO_RUN;
g := Gcd;
published := function(p, n)
  if n = 4 and p > 3 then return 4; fi;
  if n = 5 and p > 3 then return 3 + 2*g(p-1,3) + g(p-1,4); fi;
  if n = 6 and p > 5 then
    return 2*p + 7 + 4*g(p-1,3) + 4*g(p-1,4) + 2*g(p-1,5); fi;
  if n = 7 and p > 5 then
    return 2*p^2 + 5*p + 3 + (2*p+2)*g(p-1,3) + (p+4)*g(p-1,5) + g(p-1,7) + g(p-1,8); fi;
  if n = 7 and p = 5 then return 99; fi;
  return fail;
end;
t0 := Runtime();
Print("====================================================================\n");
Print("TOTAL MAXIMAL-CLASS p-GROUPS, p = ", p, "\n");
Print("====================================================================\n");
M := [ ExtraspecialGroup(p^3, p), ExtraspecialGroup(p^3, p^2) ];
Print("Order ", p, "^3: ", Length(M), " (two extraspecial groups)\n");
for n in [4..N_MAX] do
  tn := Runtime();
  newM := [];
  parents_with_child := 0;
  nonmax := 0;
  for G in M do
    D := PqDescendants(G : StepSize := 1);
    mc := Filtered(D, H -> NilpotencyClassOfGroup(H) = n-1);
    nonmax := nonmax + Length(D) - Length(mc);
    if Length(mc) > 0 then parents_with_child := parents_with_child + 1; fi;
    Append(newM, mc);
  od;
  M := newM;
  sg := "n/a";
  if ID_AVAILABLE(p^n) <> fail then
    sg := Number(AllSmallGroups(p^n), H -> NilpotencyClassOfGroup(H) = n-1);
  fi;
  pub := published(p, n);
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
  Print(" | ", Runtime()-tn, " ms\n");
od;
Print("Total runtime: ", Runtime()-t0, " ms\n");
QUIT;
