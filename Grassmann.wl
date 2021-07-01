(* ::Package:: *)
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

GrassmannQ[_] := False
GrassmannQ[_SignatureBundle] := True
GrassmannQ[_SubManifold] := True
GrassmannQ[_MultiVector] := True
ManifoldQ[_] := False
ManifoldQ[_SignatureBundle] := True
ManifoldQ[_SubManifold] := True
GradedQ[_] := False
GradedQ[_SubManifold] := True
SubManifoldQ[_] := False
SubManifoldQ[_SubManifold] := True
MultiVectorQ[_] := False
MultiVectorQ[_MultiVector] := True
BasisQ[_SubManifold] := False
BasisQ[_SignatureBundle] := False
BasisQ[SubManifold[M_SubManifold, G_, B_]] := True

IndexLimit=20;SparseLimit=22;
CountOnes[d_Integer]:=CountOnes[d]=DigitCount[d,2,1]
BinomialSum[n_Integer,m_Integer] :=
 BinomialSum[n,m]= If[m==0,0,BinomialSum[n,m-1]+Binomial[n,m-1]]
Combinations[n_Integer,m_Integer]:=Combinations[n,m]=Subsets[Range[n],{m}]
Indices[n_Integer]:=Flatten@Position[Reverse[IntegerDigits[n,2]],1]
BladeIndexCalc[d_Integer,n_Integer]:=
 (Flatten@Position[Combinations[n,CountOnes[d]],Indices[d]])[[1]]
BladeIndex[n_Integer,d_Integer]:=If[n>20,BladeIndexCalc[d,n],
 BladeIndex[d,n]=BladeIndexCalc[d,n]]
BasisIndexCalc[d_,n_]:=BinomialSum[n,CountOnes[d]]+BladeIndex[n,d]
BasisIndex[n_Integer,d_Integer]:=If[n>20,BasisIndexCalc[d,n],
 BasisIndex[n,d]=BasisIndexCalc[d,n]]
IndexToInteger[c_,n_Integer]:=FromDigits[Reverse[Table[Boole[MemberQ[c,i]],{i,n}]],2]
IndexBasisCalc[n_Integer,g_Integer]:=Map[IndexToInteger[#,n]&,Combinations[n,g]]
IndexBasis[n_Integer,g_Integer]:=If[n>SparseLimit,IndexBasisCalc[n,g],
 IndexBasis[n,g]=IndexBasisCalc[n,g]]
IndexBasisSet[n_Integer] := Flatten[Table[IndexBasis[n, i], {i, 0, n}]]

BitIndex[s_Integer, i_Integer] := BitIndex[s, i] = Module[
 {b = BitShiftLeft[1, i - 1]}, BitAnd[b, s] == b]
BitIndex[s_Integer, i_] := Map[BitIndex[s, #] &, i]
doc2m[d_, o_, c_ : 0, q_ : 0] := doc2m[d,o,c,q] =
 BitOr[BitShiftLeft[1, d - 1], BitShiftLeft[1, 2 o - 1], 
  If[c < 0, 8, BitShiftLeft[1, 3 c - 1]], BitShiftLeft[1, 5 q - 1]]

Manifold[V_SignatureBundle] := V
Manifold[V_SubManifold] := V
Manifold[SubManifold[M_SubManifold, G_, B_]] := M
Manifold[SubManifold[M_Integer, G_, B_]] := M

SignatureBundle /: Part[SignatureBundle[n___], i_] := BitIndex[0, i]
SignatureBundle /: Part[SignatureBundle[n_, m_, s_, f___], i_] := BitIndex[s, i]
(*SignatureBundle[n_,o_:0,s_:0,v_:0]:=SignatureBundle[n,o,s,v,0]*)

SubManifold[V_,G_] := SubManifold[V, G, BitShiftLeft[1, G] - 1]
SubManifold[V_SubManifold] := SubManifold[V, Grade[V]]
SubManifold[V_SignatureBundle] := SubManifold[V, Rank[V]]
SubManifold[V_Integer] := SubManifold[V,V]
SubManifold[M_, b_List] := SubManifold[M, Length[b], IndexToInteger[b, Dims[M]]]
SubManifold /: Part[SubManifold[V__Integer], i_] := True
SubManifold /: Part[SubManifold[SignatureBundle[n_, m_, s_, f___], G_, B_], i_] := BitIndex[s, Indices[B][[i]]]
SubManifold /: Part[SubManifold[SubManifold[v_, g_, s_], G_, B_], i_] := BitIndex[s, i]
SubManifold /: Subscript[SubManifold[V_, G_, B_], i___] := SubManifold[V, {i}]
SubManifold[V_, G_, B_][i___] := SubManifold[V, {i}]

SuperManifold[n_Integer] := n
SuperManifold[m_SignatureBundle] := m
SuperManifold[SubManifold[M_, G_, B_]] := M
Parent[V_] := Manifold[V]

SignatureBundle /: Det[s_SignatureBundle] := If[OddQ[CountOnes[Metric[s]]], -1, 1]
SignatureBundle /: Abs[s_SignatureBundle] := Sqrt[Abs[Det[s]]]
SubManifold /: Abs[s_SubManifold] := If[BasisQ[s], Sqrt[Reverse[s] s], Sqrt[Abs[Det[s]]]]

Indices[SubManifold[V_, G_, B_]] := Indices[B]

Rank[n_Integer] := n
Rank[SignatureBundle[n_, m___]] := n
Rank[SubManifold[V_, G_, B_]] := G
Grade[V_SignatureBundle] := Rank[V] - If[DyadicQ[V], 2, 2]*DiffVars[V]
Grade[V_SubManifold] := Rank[V] - If[DyadicQ[V], 2, 1]*DiffVars[V]
Dims[M_] := Dims[Manifold[M]]
Dims[M_Integer] := M
Dims[V_SignatureBundle] := Rank[V]
Dims[SubManifold[M_, G_, B_]] := G
Dims[SubManifold[M_SubManifold, G_, B_]] := Dims[M]

vio = {"\[Infinity]", "\[EmptySet]"}
printsep[_, _SignatureBundle, _, _] := Nothing
printsep[_, _Integer, _, _] := Nothing
printsep[out_, s_, k_, n_] := k != n && AppendTo[out, ","]
sig[_Integer, _] := "x"(*"\[Times]"*)
sig[s_, k_] := s[[k]]
sig[s_SignatureBundle, k_] := If[s[[k]], "-", "+"]
NamesIndex[x_] := 1

Labels[n_, v_ : "v"] := Map[Symbol[v <> StringJoin[Map[ToString, Indices[#]]]] &, IndexBasisSet[n]]
Generate[V_SubManifold] := Map[SubManifold[V, CountOnes[#], #] &, IndexBasisSet[Rank[V]]]
Generate[V_] := Generate[SubManifold[V]]
Basis[V_] := Basis[SubManifold[V]]
Basis[V_SubManifold] := Set @@@ Transpose[{Unevaluated /@ Labels[Rank[V]], Generate[V]}]

SignatureBundle /: MakeBoxes[s_SignatureBundle, StandardForm] := Module[{dm,out,y,d,n},
 dm = DiffQ[s]; out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], 2],
    "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}]; y = DyadQ[s]; 
 d = DiffVars[s]; n = Dims[s] - If[d > 0, If[y < 0, 2 d, d], 0]; 
 InfinityQ[s] && AppendTo[out, vio[[1]]]; 
 OriginQ[s] && AppendTo[out, vio[[2]]];
 d < 0 && AppendTo[out, SubscriptBox[Nothing, Range[Abs[d], 1, -1]]];
 out = Join[out, Map[If[#, "-", "+"] &, 
    s[[Range[Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], n]]]]];
 d > 0 && AppendTo[out, If[BitXor[Boole[y > 0], Boole[!PolyQ[s]]]>0, 
    SuperscriptBox[Nothing, Range[1, Abs[d]]], 
    SubscriptBox[Nothing, Range[1, Abs[d]]]]];
 d > 0 && y < 0 && AppendTo[out, SuperscriptBox[Nothing, Range[1, Abs[d]]]];
 AppendTo[out, "\[RightAngleBracket]"];
 y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
 NamesIndex[s] > 1 && AppendTo[out, SubscriptBox[Nothing, subs[NamesIndex[s]]]];
 RowBox[out]]

SubManifold /: MakeBoxes[s_SubManifold, StandardForm] := 
 If[BasisQ[s], SubscriptBox[MakeBoxes[v], RowBox[Riffle[Indices[s], ","]]],
  Module[{V,P,PnV,M,dm,out,y,d,dM,ind,n,nM},
  V = SuperManifold[s]; P = If[IntegerQ[V], V, Parent[V]]; PnV = P != V;
  M = If[PnV, SuperManifold[P], V]; dm = DiffQ[s]; 
  out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], 2], 
     "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}];
  PnV && PrependTo[out, SuperscriptBox["\[CapitalLambda]", Rank[V]]];
  y = DyadQ[s]; d = DiffVars[s]; dM = DiffVars[M]; ind = Indices[s];
  n = Grade[s] - If[d > 0, If[y < 0, 2 d, d], 0];
  NM = Dims[M] - If[dM > 0, If[y < 0, 2 dM, dM], 0];
  InfinityQ[s] && AppendTo[out, vio[[1]]]; 
  OriginQ[s] && AppendTo[out, vio[[2]]];
  Do[AppendTo[out, If[MemberQ[ind, k], sig[M, k], "_"]]; printsep[out, M, k, Grade[s]];,
   {k, Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], NM}];
  d > 0 && AppendTo[out, If[BitXor[(y > 0), ! PolyQ[s]], 
   SuperscriptBox[Nothing, ind[[Range[n + 1, n + Abs[d]]]] - NM], 
   SubscriptBox[Nothing, ind[[Range[n + 1, n + Abs[d]]]] - NM]]];
  d > 0 && y < 0 && AppendTo[out, 
   SuperscriptBox[Nothing, ind[[Range[n + Abs[d] + 1, Length[ind]]]] - NM]];
  AppendTo[out, "\[RightAngleBracket]"];
  y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
  NamesIndex[s] > 1 && AppendTo[out, SubscriptBox[Nothing, subs[NamesIndex[s]]]];
  PnV && AppendTo[out, "\[Times]" <> ToString[Length[V]]];
  RowBox[out]]]

PolyQCalc[M_Integer] := BitAnd[M, 16] == 0
DyadQCalc[M_Integer] := If[MemberQ[Range[8, 11], Mod[M, 16]], -1, 
  Boole[MemberQ[{4, 5, 6, 7}, Mod[M, 16]]]]
InfinityQCalc[M_Integer] := MemberQ[{1, 3, 5, 7, 9, 11}, Mod[M, 16]]
OriginQCalc[M_Integer] := MemberQ[{2, 3, 6, 7, 10, 11}, Mod[M, 16]]

PolyQ[_Integer] := True
Map[(#[_Integer] := 0) &, {OptionsQ, DyadQ, DiffQ, DiffVars}]
Map[(#[t_] := #[Manifold[t]]) &, {OptionsQ, PolyQ, DyadQ, DiffQ, DiffVars}]
PolyQ[SignatureBundle[N_, M_, S___]] := PolyQCalc[M]
DyadQ[SignatureBundle[N_, M_, S___]] := DyadQCalc[M]
DiffQ[SignatureBundle[N_, M_, S_, F_, D_]] := D
DiffVars[SignatureBundle[N_, M_, S_, F_, D___]] := F
SignatureBundle /: Signature[SignatureBundle[N_, M_, S_, F___]] := S
SignatureBundle /: Signature[_SignatureBundle] := 0
OptionsQ[SignatureBundle[N_, M_, S___]] := M
PolyQ[_SignatureBundle] := PolyQCalc[0]
DyadQ[_SignatureBundle] := DyadQCalc[0]
DiffQ[_SignatureBundle] := 0
DiffVars[_SignatureBundle] := 0
OptionsQ[_SignatureBundle] := 0
Map[(#[SubManifold[V_, G_, B_]] := #[V]) &, {OptionsQ, Metric, PolyQ, DyadQ, DiffQ}]
DiffVars[SubManifold[M_, N_, S_]] := Module[{n = Dims[M], c = DiffQ[M]},
  Total[Map[Boole[MemberQ[Range[1+n-If[c<0,2,1]*DiffVars[M],n],#]] &,Indices[S]]]]
(*SubManifold/:Basis[Times[V_SubManifold,a__]]:=V*)

DyadicQ[t_] := DyadQ[Manifold[t]] < 0
DualQ[t_] := DyadQ[Manifold[t]] > 0
TangentQ[t_] := DiffVars[Manifold[t]] != 0

Metric[_Integer] := 0
Metric[V_, b_Integer] := Times@@Map[Boole,V[[Indices[b]]]]

InfinityQ[_Integer] := False
InfinityQ[_SignatureBundle] := InfinityQCalc[0]
InfinityQ[SignatureBundle[N_, M_, S___]] := InfinityQCalc[M]
InfinityQ[SubManifold[M_, N_, S_]] := InfinityQ[M] && OddQ[S]
(*InfinityQ[Times[a_SubManifold,b__]]:=InfinityQ[a]*)

OriginQ[_Integer] := False
OriginQ[_SignatureBundle] := OriginQCalc[0]
OriginQ[SignatureBundle[N_, M_, S___]] := OriginQCalc[M]
OriginQ[SubManifold[M_, N_, S_]] := 
 OriginQ[M] && If[InfinityQ[M], BitAnd[2, S] == 2, OddQ[S]]
(*OriginQ[Times[a_SubManifold,b__]]:=OriginQ[a]*)

(*isinf[e_SubManifold]:=InfinityQ[e]&&Grade[e]==1
isorigin[SubManifold[V_,G_,B_]]:=OriginQ[V]&&G==1&&e[InfiniftyQ[V]+1]*)

ConformalQ[V_] := InfinityQ[V] && OriginQ[V]
OriginQ[V_, B_Integer] := If[InfinityQ[V], BitAnd[2, B] == 2, OddQ[B]]
InfinityQ[V_, A_Integer, B_Integer] := ConformalQ[V] && (OddQ[A] || OddQ[B])
OriginQ[V_, A_Integer, B_Integer] := ConformalQ[V] && (OriginQ[V, A] || OriginQ[V, B])
Infinity2Q[V_, A_Integer, B_Integer] := ConformalQ[V] && OddQ[A] && OddQ[B]
Origin2Q[V_, A_Integer, B_Integer] := ConformalQ[V] && OriginQ[V, A] && OriginQ[V, B]
OriginInfinityQ[V_, A_Integer, B_Integer] := 
 ConformalQ[V] && OriginQ[V, A] && OddQ[B] && (! OriginQ[V, B]) && (! OddQ[A])
InfinityOriginQ[V_, A_Integer, B_Integer] := 
 ConformalQ[V] && OddQ[A] && OriginQ[V, B] && (! OddQ[B]) && (! OriginQ[V, A])
Infinity2OriginQ[V_, A_Integer, B_Integer] := Infinity2Q[V, A, B] && OriginQ[V, A, B]
Origin2InfinityQ[V_, A_Integer, B_Integer] := Origin2Q[V, A, B] && InfinityQ[V, A, B]

Twiddle[d_Integer] := BitXor[d, BitShiftLeft[1, 64] - 1]

DiffMask[_Integer] := 0
DiffMask[V_] := Module[{d = DiffVars[V], typemax = BitShiftLeft[1, 64] - 1},
  If[DyadicQ[V], Module[{
    v = BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[V] - 2 d],
    w = BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[V] - d]},
    If[d < 0, {typemax - v, typemax - w}, {v, w}]],
   Module[{v = BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[V] - d]},
   If[d < 0, typemax - v, v]]]]
SymmetricSplit[V_, a_] := Module[{sm = SymmetricMask[V, a], dm = DiffMask[V]},
  If[DyadicQ[V], {BitAnd[sm, dm[1]], BitAnd[sm, dm[2]]}, sm]]
SymmetricMask[V_, a_] := Module[{d = DiffMask[V]},
  BitAnd[a, If[DyadicQ[V], BitOr[d[[1]], d[[2]]], d]]]
SymmetricMask[V_, a_, b_] := Module[{d = DiffMask[V],dD,aD,bD},
  dD = If[DyadicQ[V], BitOr[d[[1]], d[[2]]], d];
  aD = BitAnd[a, dD]; bD = BitAnd[b, dD];
  {BitAnd[a, Twiddle[dD]], BitAnd[b, Twiddle[D]], BitOr[aD, bD], 
   BitAnd[aD, bD]}]
DiffCheck[V_, A_Integer, B_Integer] := Module[{
  d = DiffVars[V], db = DiffMask[V], v, hi, ho},
  v = If[DyadicQ[V], BitOr[db[1], db[2]], db];
  hi = Infinity2Q[V, A, B] && ! OriginQ[V, A, B];
  ho = Origin2Q[V, A, B] && ! InfinityQ[V, A, B];
  (hi || ho) || (d != 0 && 
     CountOnes[BitAnd[A, v]] + CountOnes[BitAnd[B, v]] > DiffMode[V])]

flipsig[N_, S_Integer] := BitAnd[2^N - 1, Twiddle[S]]

Dual[V_] := If[DyadicQ[V], V, V^T]
Dual[V_, B_, M_ : Rank[V]/2] := 
 BitOr[BitAnd[BitShiftLeft[B, M], BitShiftLeft[1, Rank[V]] - 1], 
  BitShiftLeft[B, M]]

SignatureBundle /: Transpose[V_SignatureBundle] := Module[{c = DyadQ[V]},
 c < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 SignatureBundle[Rank[V], 
  doc2m[Boole[InfinityQ[V]], Boole[OriginQ[V]], If[c > 0, 0, 1]], 
  flipsig[Rank[V], Signature[V]], DiffVars[V], DiffQ[V]]]
SubManifold /: Transpose[SubManifold[M_, N_, S_]] := Module[{},
 DyadQ[M] < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 SubManifold[If[IntegerQ[M], Transpose[SignatureBundle[M]], Transpose[M]], N, S]]

