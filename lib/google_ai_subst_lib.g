# Substitution matrices: row convention, basis x^1..x^n of F_p[x]/(x^{n+1}).
SubstMat := function(p, n, s)
  local F, x, sx, M, k, pk, j, c;
  F := GF(p); x := Indeterminate(F, "x");
  sx := Sum([1..n], j -> s[j]*One(F)*x^j);
  M := NullMat(n, n, F);
  pk := One(F)*x^0;
  for k in [1..n] do
    pk := pk*sx;
    c := CoefficientsOfUnivariatePolynomial(pk);
    for j in [k..n] do
      if j+1 <= Length(c) then M[k][j] := c[j+1]; fi;
    od;
  od;
  return M;
end;
Xk := function(n, k)
  local s; s := List([1..n], j -> 0); s[1] := 1; s[k] := 1; return s;
end;
