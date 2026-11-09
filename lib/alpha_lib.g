# alpha_lib.g
# Library for the 1982 parametric family of order-5^7 descendants of E_5 =~ G(5, 5),
# parameterized by alpha = [alpha_1, ..., alpha_6] in (Z/5Z)^6 (Section 5 of the paper).

Read("lib/klg_lib.g");

# Polycyclic collector for G(alpha) on generators x_1, ..., x_7 of order 5^7.
DescColl := function(a)
  local F, x, c;
  F := FreeGroup(7);
  x := GeneratorsOfGroup(F);
  c := SingleCollector(F, [5, 5, 5, 5, 5, 5, 5]);
  SetPower(c, 1, x[7]^a[5]);
  SetPower(c, 2, x[6]^4 * x[7]^a[6]);
  SetPower(c, 3, x[7]^4);
  SetCommutator(c, 2, 1, x[3]);
  SetCommutator(c, 3, 1, x[4]);
  SetCommutator(c, 4, 1, x[5]);
  SetCommutator(c, 5, 1, x[6]);
  SetCommutator(c, 6, 1, x[7]);
  SetCommutator(c, 3, 2, x[5] * x[7]^a[1]);
  SetCommutator(c, 4, 2, x[6] * x[7]^a[2]);
  SetCommutator(c, 5, 2, x[7]^a[3]);
  SetCommutator(c, 4, 3, x[7]^a[4]);
  UpdatePolycyclicCollector(c);
  return c;
end;

# Construct the PcGroup G(alpha) for a consistent parameter tuple alpha.
DescGroup := function(a)
  local c;
  c := DescColl(a);
  if not IsConfluent(c) then
    Error("Inconsistent parameter tuple alpha = ", a);
  fi;
  return GroupByRwsNC(c);
end;

# Return all 625 consistent parameter tuples alpha in {0..4}^6
# (characterized by alpha_3 + alpha_4 === 1 and alpha_2 === alpha_3 - 1 (mod 5)).
ConsistentAlphas := function()
  return Filtered(Tuples([0..4], 6), a -> IsConfluent(DescColl(a)));
end;

# Shared worker for scripts/exhaustive_5_7/job0.g .. job5.g:
# For all consistent tuples cons[i] with i === rem (mod 6), lifts every conjugacy class
# of extreme stabilizers T <= E_5 = G/V (where V = <x_6, x_7>) to its preimage P <= G,
# enumerates all core-free maximal subgroups H < P of order 125 with |H \cap V| = 5,
# and writes the distribution of f(G, H) to outfile.
RunExhaustive57Job := function(rem, outfile)
  local cons, G0, x0, V0, hom0, Q0, extQ0, extP_exps,
        out, i, a, G, x, V, fs, exps, P, H, S, f24;
  cons := ConsistentAlphas();
  # Because alpha_1..alpha_6 only enter the exponents of x_6 and x_7 in V = <x_6, x_7>,
  # the quotient Q = G/V =~ E_5 and its 25 conjugacy classes of extreme stabilizers
  # have identical polycyclic generator words in x_1..x_7 for every consistent tuple a.
  G0 := DescGroup(cons[1]);
  x0 := Pcgs(G0);
  V0 := Subgroup(G0, [x0[6], x0[7]]);
  hom0 := NaturalHomomorphismByNormalSubgroup(G0, V0);
  Q0 := Image(hom0);
  extQ0 := Filtered(List(ConjugacyClassesSubgroups(Q0), Representative),
                    T -> Size(T) = 25 and Size(Core(Q0, T)) = 1 and 6 * UltraFastF(Q0, T) = Size(Q0) + 1);
  extP_exps := List(extQ0,
                    T -> List(GeneratorsOfGroup(PreImage(hom0, T)), g -> ExponentsOfPcElement(x0, g)));

  out := OutputTextFile(outfile, false);
  SetPrintFormattingStatus(out, false);
  for i in [1..Length(cons)] do
    if i mod 6 = rem then
      a := cons[i];
      G := DescGroup(a);
      x := Pcgs(G);
      V := Subgroup(G, [x[6], x[7]]);
      fs := [];
      for exps in extP_exps do
        P := Subgroup(G, List(exps, e -> PcElementByExponents(x, e)));
        for H in MaximalSubgroups(P) do
          if Size(Intersection(H, V)) = 5 and not (x[7] in H) and Size(Core(G, H)) = 1 then
            Add(fs, UltraFastF(G, H));
          fi;
        od;
      od;
      S := Subgroup(G, [x[2], x[4]]);
      if Size(S) = 125 and Size(Core(G, S)) = 1 then
        f24 := UltraFastF(G, S);
      else
        f24 := -Size(S);
      fi;
      AppendTo(out, a, ";", Length(extQ0), ";", Length(fs), ";", f24, ";", Collected(fs), ";",
               Maximum(Concatenation(fs, [0])), ";", NrConjugacyClasses(G), ";", Size(Centre(G)), "\n");
    fi;
  od;
  CloseStream(out);
end;
