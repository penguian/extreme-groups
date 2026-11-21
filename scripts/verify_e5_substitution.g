# verify_e5_substitution.g
# Verify that the substitution group modulo x^7 over F_5 is isomorphic to E_5
# and coincides as a matrix group in UT(6, F_5) with the KLG group G(5, 5).

Read("lib/param_5_7_lib.g");
Read("lib/subst_lib.g");
Read("lib/timings_lib.g");

RunVerifyE5Substitution := function()
  local G, E5, N, P, K, isoOk, klgAreSubst;
  G := DescGroup([0, 1, 2, 4, 0, 4]);
  E5 := Image(NaturalHomomorphismByNormalSubgroup(G, Subgroup(G, [Pcgs(G)[6], Pcgs(G)[7]])));
  N := Group(List([2..6], k -> SubstMat(5, 6, Xk(6, k))));
  P := Image(IsomorphismPcGroup(N));
  isoOk := IsomorphismGroups(P, E5) <> fail;
  Print("substitution group mod x^7 over F_5: order 5^", Log(Size(P), 5),
        "; isomorphic to E_5: ", isoOk, "\n");

  # K-LG G(5,5) generators exp(u_i) from KLGmats(5, 5) are substitutions and generate N.
  K := Group(KLGmats(5, 5));
  klgAreSubst := ForAll(GeneratorsOfGroup(K), g -> SubstMat(5, 6, List(g[1], IntFFE)) = g);
  Print("K-LG G(5,5) generators are substitutions: ", klgAreSubst,
        "; equal groups: ", K = N, "\n");
  if Size(P) <> 3125 or not isoOk or not klgAreSubst or K <> N then
    Error("E_5 substitution group verification failed!");
  fi;
  PrintTimingIfEnabled();
end;

RunVerifyE5Substitution();
QUIT;
