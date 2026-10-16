Read("lib/alpha_lib.g");
Read("lib/google_ai_subst_lib.g");
G := DescGroup([0,1,2,4,0,4]);
E5 := Image(NaturalHomomorphismByNormalSubgroup(G, Subgroup(G, [Pcgs(G)[6], Pcgs(G)[7]])));
N := Group(List([2..6], k -> SubstMat(5, 6, Xk(6, k))));
P := Image(IsomorphismPcGroup(N));
Print("substitution group mod x^7 over F_5: order 5^", Log(Size(P),5), "; isomorphic to E_5: ",
      IsomorphismGroups(P, E5) <> fail, "\n");
# K-LG G(5,5) generators exp(u_i) are substitutions and generate N?
ExpNil := function(u, p)
  local r, t, k; r := u^0; t := u^0;
  for k in [1..p-1] do t := t*u/k; r := r + t; od;
  if not IsZero(u^p) then Error("u^p <> 0"); fi; return r;
end;
U := function(p, m, i)
  local mat, k; mat := NullMat(m+1, m+1, GF(p));
  for k in [1..m+1-i] do mat[k][k+i] := k*One(GF(p)); od; return mat;
end;
K := Group(List([1..5], i -> ExpNil(U(5,5,i), 5)));
Print("K-LG G(5,5) generators are substitutions: ",
      ForAll(GeneratorsOfGroup(K), g -> SubstMat(5, 6, List(g[1], IntFFE)) = g), "; equal groups: ", K = N, "\n");
QUIT;
