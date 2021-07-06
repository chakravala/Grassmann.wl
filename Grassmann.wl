(* ::Package:: *)
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

(* Submanifold -> Submanifold *)
(* guide page: explain symbols, products
standard form, *)

GrassmannQ[_] := False
GrassmannQ[_MetricSignature] := True
GrassmannQ[_Submanifold] := True
GrassmannQ[_Multivector] := True
ManifoldQ[_] := False
ManifoldQ[_MetricSignature] := True
ManifoldQ[_Submanifold] := True
GradedQ[_] := False
GradedQ[_Submanifold] := True
SubmanifoldQ[_] := False
SubmanifoldQ[_Submanifold] := True
MultivectorQ[_] := False
MultivectorQ[_Multivector] := True
BasisQ[_Submanifold] := False
BasisQ[_MetricSignature] := False
BasisQ[Submanifold[M_Submanifold, G_, B_]] := True

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
IndexBasis[n_Integer] := Flatten[Table[IndexBasis[n, i], {i, 0, n}]]

BitIndex[s_Integer, i_Integer] := BitIndex[s, i] = Module[
 {b = BitShiftLeft[1, i - 1]}, BitAnd[b, s] == b]
BitIndex[s_Integer, i_] := Map[BitIndex[s, #] &, i]
doc2m[d_, o_, c_ : 0, q_ : 0] := doc2m[d,o,c,q] =
 BitOr[BitShiftLeft[1, d - 1], BitShiftLeft[1, 2 o - 1], 
  If[c < 0, 8, BitShiftLeft[1, 3 c - 1]], BitShiftLeft[1, 5 q - 1]]

Manifold[V_MetricSignature] := V
Manifold[V_Submanifold] := V
Manifold[Submanifold[M_Submanifold, _, _]] := M
Manifold[Submanifold[M_Integer, _, _]] := M

MetricSignature /: Part[MetricSignature[___], i_] := BitIndex[0, i]
MetricSignature /: Part[MetricSignature[_, _, s_, ___], i_] := BitIndex[s, i]
(*MetricSignature[n_,o_:0,s_:0,v_:0]:=MetricSignature[n,o,s,v,0]*)

Submanifold[V_,G_] := Submanifold[V, G, BitShiftLeft[1, G] - 1]
Submanifold[V_Submanifold] := Submanifold[V, Rank[V]]
Submanifold[V_MetricSignature] := Submanifold[V, Rank[V]]
Submanifold[V_Integer] := Submanifold[V,V]
Submanifold[M_, b_List] := Submanifold[M, Length[b], IndexToInteger[b, Dims[M]]]
Submanifold /: Part[Submanifold[V__Integer], i_] := True
Submanifold /: Part[Submanifold[MetricSignature[_, _, s_, ___], _, B_], i_] := BitIndex[s, Indices[B][[i]]]
Submanifold /: Part[Submanifold[Submanifold[_, _, s_], _, _], i_] := BitIndex[s, i]
Submanifold /: Subscript[Submanifold[V_, _, _], i___] := Submanifold[V, {i}]
Submanifold[V_, _, _][i___] := Submanifold[V, {i}]

Supermanifold[n_Integer] := n
Supermanifold[m_MetricSignature] := m
Supermanifold[Submanifold[M_, _, _]] := M
Parent[V_] := Manifold[V]

MetricSignature /: Det[s_MetricSignature] := If[OddQ[CountOnes[Metric[s]]], -1, 1]
MetricSignature /: Abs[s_MetricSignature] := Sqrt[Abs[Det[s]]]
Submanifold /: Abs[s_Submanifold] := If[BasisQ[s], Sqrt[Reverse[s] s], Sqrt[Abs[Det[s]]]]

Indices[Submanifold[_, _, B_]] := Indices[B]

Bits[Submanifold[_,_,B_]] := B
Rank[n_Integer] := n
Rank[MetricSignature[n_, ___]] := n
Rank[Submanifold[_, G_, _]] := G
Grade[V_MetricSignature] := Rank[V] - If[DyadicQ[V], 2, 2]*DiffVars[V]
Grade[V_Submanifold] := Rank[V] - If[DyadicQ[V], 2, 1]*DiffVars[V]
Dims[M_] := Dims[Manifold[M]]
Dims[M_Integer] := M
Dims[V_MetricSignature] := Rank[V]
Dims[Submanifold[_, G_, _]] := G
Dims[Submanifold[M_Submanifold, _, _]] := Dims[M]

vio = {"\[Infinity]", "\[EmptySet]"}
printsep[_, _MetricSignature, _, _] := Nothing
printsep[_, _Integer, _, _] := Nothing
printsep[out_, _, k_, n_] := k != n && AppendTo[out, ","]
sig[_Integer, _] := "x"(*"\[Times]"*)
sig[s_, k_] := s[[k]]
sig[s_MetricSignature, k_] := If[s[[k]], "-", "+"]
NamesIndex[x_] := 1

Labels[n_, v_String:"v"] := Labels[IndexBasis[Rank[n]],v]
Labels[n_, g_, v_String:"v"] := Labels[IndexBasis[Rank[n],g],v]
Labels[b_List,v_String] := Map[Symbol[v <> StringJoin[Map[ToString, Indices[#]]]] &, b]
GeometricAlgebraBasis[V_Submanifold] := GeometricAlgebraBasis[V,IndexBasis[Rank[V]]]
GeometricAlgebraBasis[V_Submanifold,g_] := GeometricAlgebraBasis[V,IndexBasis[Rank[V],g]]
GeometricAlgebraBasis[V_Submanifold,b_List] := Map[Submanifold[V, CountOnes[#], #] &, b]
GeometricAlgebraBasis[V_] := GeometricAlgebraBasis[Submanifold[V]]
AllocateBasis[V_] := AllocateBasis[Submanifold[V]]
AllocateBasis[V_Submanifold] := Set @@@ Transpose[{Unevaluated /@ Labels[V], GeometricAlgebraBasis[V]}]

SymbolQ[_Symbol] := True
SymbolQ[_] := False

MetricSignature /: MakeBoxes[s_MetricSignature, StandardForm] := Module[{dm,out,y,d,n},
 dm = DiffQ[s]; out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], If[SymbolQ[dm],MakeBoxes[dm],dm]],
    "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}]; y = DyadQ[s]; 
 d = DiffVars[s]; n = Dims[s] - If[d > 0, If[y < 0, 2 d, d], 0]; 
 InfinityQ[s] && AppendTo[out, vio[[1]]]; 
 OriginQ[s] && AppendTo[out, vio[[2]]];
 d < 0 && AppendTo[out, SubscriptBox["", Sequence @@ Range[Abs[d], 1, -1]]];
 out = Join[out, Map[If[#, "-", "+"] &, 
    s[[Range[Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], n]]]]];
 d > 0 && AppendTo[out, If[BitXor[Boole[y > 0], Boole[!PolyQ[s]]]>0, 
    SuperscriptBox["", Range[1, Abs[d]]],
    SubscriptBox["", Sequence @@ Range[1, Abs[d]]]]];
 d > 0 && y < 0 && AppendTo[out, SuperscriptBox["", Range[1, Abs[d]]]];
 AppendTo[out, "\[RightAngleBracket]"];
 y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
 NamesIndex[s] > 1 && AppendTo[out, SubscriptBox["", subs[NamesIndex[s]]]];
 RowBox[out]]

Submanifold /: MakeBoxes[s_Submanifold, StandardForm] :=
 If[BasisQ[s], PrintIndices[Supermanifold[s],Bits[s]],
  Module[{V,P,PnV,M,dm,out,y,d,dM,ind,n,nM},
  V = Supermanifold[s]; P = If[IntegerQ[V], V, Parent[V]]; PnV = P != V;
  M = If[PnV, Supermanifold[P], V]; dm = DiffQ[s];
  out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], If[SymbolQ[dm],MakeBoxes[dm],dm]],
     "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}];
  PnV && PrependTo[out, SuperscriptBox["\[CapitalLambda]", Rank[V]]];
  y = DyadQ[s]; d = DiffVars[s]; dM = DiffVars[M]; ind = Indices[s];
  n = Rank[s] - If[d > 0, If[y < 0, 2*d, d], 0];
  NM = Dims[M] - If[dM > 0, If[y < 0, 2*dM, dM], 0];
  InfinityQ[s] && AppendTo[out, vio[[1]]]; 
  OriginQ[s] && AppendTo[out, vio[[2]]];
  Do[AppendTo[out, If[MemberQ[ind, k], sig[M, k], "_"]]; printsep[out, M, k, Grade[s]];,
   {k, Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], NM}];
  d > 0 && AppendTo[out, If[BitXor[Boole[y > 0], !PolyQ[s]],
   SuperscriptBox["", RowBox[Riffle[ind[[Range[n+1, n+Abs[d]]]] - NM, ","]]],
   SubscriptBox["", RowBox[Riffle[ind[[Range[n+1, n+Abs[d]]]] - NM, ","]]]]];
  d > 0 && y < 0 && AppendTo[out, 
   SuperscriptBox["", RowBox[Riffle[ind[[Range[n+Abs[d]+1,Length[ind]]]]-NM,","]]]];
  AppendTo[out, "\[RightAngleBracket]"];
  y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
  NamesIndex[s] > 1 && AppendTo[out, SubscriptBox["", subs[NamesIndex[s]]]];
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
PolyQ[MetricSignature[_, M_, ___]] := PolyQCalc[M]
DyadQ[MetricSignature[_, M_, ___]] := DyadQCalc[M]
DiffQ[MetricSignature[_, _, _, _, D_]] := D
DiffVars[MetricSignature[_, _, _, F_, ___]] := F
MetricSignature /: Signature[MetricSignature[_, _, S_, ___]] := S
MetricSignature /: Signature[_MetricSignature] := 0
OptionsQ[MetricSignature[_, M_, ___]] := M
PolyQ[_MetricSignature] := PolyQCalc[0]
DyadQ[_MetricSignature] := DyadQCalc[0]
DiffQ[_MetricSignature] := 0
DiffVars[_MetricSignature] := 0
OptionsQ[_MetricSignature] := 0
Map[(#[Submanifold[V_, _, _]] := #[V]) &, {OptionsQ, Metric, PolyQ, DyadQ, DiffQ}]
DiffVars[Submanifold[M_, _, S_]] := Module[{n = Dims[M], c = DiffQ[M]},
  Total[Map[Boole[MemberQ[Range[1+n-If[c<0,2,1]*DiffVars[M],n],#]] &,Indices[S]]]]
(*Submanifold/:Basis[Times[V_Submanifold,a__]]:=V*)

DyadicQ[t_] := DyadQ[Manifold[t]] < 0
DualQ[t_] := DyadQ[Manifold[t]] > 0
TangentSpaceQ[t_] := DiffVars[Manifold[t]] != 0

Metric[_Integer] := 0
Metric[V_, b_Integer] := Times@@Map[Boole,V[[Indices[b]]]]

InfinityQ[_Integer] := False
InfinityQ[_MetricSignature] := InfinityQCalc[0]
InfinityQ[MetricSignature[_, M_, ___]] := InfinityQCalc[M]
InfinityQ[Submanifold[M_, _, S_]] := InfinityQ[M] && OddQ[S]
(*InfinityQ[Times[a_Submanifold,__]]:=InfinityQ[a]*)

OriginQ[_Integer] := False
OriginQ[_MetricSignature] := OriginQCalc[0]
OriginQ[MetricSignature[_, M_, ___]] := OriginQCalc[M]
OriginQ[Submanifold[M_, _, S_]] :=
 OriginQ[M] && If[InfinityQ[M], BitAnd[2, S] == 2, OddQ[S]]
(*OriginQ[Times[a_Submanifold,__]]:=OriginQ[a]*)

(*isinf[e_Submanifold]:=InfinityQ[e]&&Grade[e]==1
isorigin[Submanifold[V_,G_,_]]:=OriginQ[V]&&G==1&&e[InfiniftyQ[V]+1]*)

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

TangentSpace[s_MetricSignature,d_:1] := Module[{f=DiffVars[s]},TangentSpace[s,d,If[f!=0,f,1]]]
TangentSpace[s:MetricSignature[n:Repeated[_,{1,3}]],d_] := TangentSpace[s,d,1]
TangentSpace[s:MetricSignature[_,_,_,0,___],d_] := TangentSpace[s,d,1]
TangentSpace[s_MetricSignature,d_,f_] := MetricSignature[Rank[s]+If[DyadicQ[s], 2*f, f],OptionsQ[s],Signature[s],f,DiffQ[s]+d]
T = TangentSpace
TangentSpace /: Power[TangentSpace,mu_] := TangentSpace[mu]
TangentSpace /: Times[TangentSpace[mu_],V_] := TangentSpace[V,mu]

Subtangent[V_] := Subscript[V,Range[Grade[V]+1,Dims[V]]]

flipsig[N_, S_Integer] := BitAnd[2^N - 1, Twiddle[S]]

Dual[V_] := If[DyadicQ[V], V, V^T]
Dual[V_, B_, M_ : Rank[V]/2] := 
 BitOr[BitAnd[BitShiftLeft[B, M], BitShiftLeft[1, Rank[V]] - 1], 
  BitShiftLeft[B, M]]

MetricSignature /: Transpose[V_MetricSignature] := Module[{c = DyadQ[V]},
 c < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 MetricSignature[Rank[V],
  doc2m[Boole[InfinityQ[V]], Boole[OriginQ[V]], If[c > 0, 0, 1]], 
  flipsig[Rank[V], Signature[V]], DiffVars[V], DiffQ[V]]]
Submanifold /: Transpose[Submanifold[M_, N_, S_]] := Module[{},
 DyadQ[M] < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 Submanifold[If[IntegerQ[M], Transpose[MetricSignature[M]], Transpose[M]], N, S]]

pre = {"v","w","\[PartialD]","\[Epsilon]"}
char[-1] := vio[[1]]
char[0] := vio[[2]]
char[i_Integer] := i
EmptyQ[set_] := Length[set] == 0

IndexText[v_, i_] := v <> StringJoin[ToString /@ i]
SubText[v_, i_, True] := IndexText[v, i]
SubText[v_, i_, False] := SubscriptBox[v, i]
SubText[v_, i_List, False] := SubscriptBox[v, RowBox[Riffle[i, ","]]]
SuperText[v_, i_, True] := IndexText[v, i]
SuperText[v_, i_, False] := SuperscriptBox[v, RowBox[Riffle[i, ","]]]

ShiftIndices[V_, b_Integer] := ShiftIndices[Supermanifold[V], b]
ShiftIndices[s_, set:List[___]] := Module[{M = Supermanifold[s]},
    EmptyQ[set] && Module[{k = 1, n = Length[set]},
        InfinityQ[M] && set[[1]] == 1 && (set[[1]] = -1; k += 1);
        shift = InfinityQ[M] + OriginQ[M]
        OriginQ[M] && n>=k && set[[k]]==shift && (set[[k]]=0;k+=1)
        shift > 0 && (set[[k;;n]] -= shift)];set]

ShiftIndices[V_Integer,b_Integer] := Indices[b]
ShiftIndices[s_Integer,set_List[___Integer]] := set

ShiftIndices[V_MetricSignature,b_Integer] := ShiftIndices[V,Indices[b]]
ShiftIndices[V:SubManifold[_,_,S_],b_Integer] := ShiftIndices[V,Indices[S][Indices[b]]]

PrintIndices[V_,e_Integer,label:(_?BooleanQ):False] := PrintLabel[V,e,label,Sequence @@ pre]

PrintIndex[i_] := char[If[i>36, i-26, i]]
PrintIndices[b_Integer] := PrintIndices[Indices[b]]
PrintIndices[b_List] := Map[PrintIndex, b]
PrintIndices[a_,b_,l:(_?BooleanQ):False,e:(_String):pre[[1]],f:(_String):pre[[2]]] := PrintIndices[a,b,{},{},l,e,f]
PrintIndices[a_,b_,c_,d_,l:(_?BooleanQ):False,e:(_String):pre[[1]],f:(_String):pre[[2]],g:(_String):pre[[3]],h:(_String):pre[[4]]] := Module[
    {aa = EmptyQ[a], bb = !EmptyQ[b], cc = !EmptyQ[c], dd = !EmptyQ[d],
    PRE = {e,f,g,h}, out},
	out = {};
    cc && AppendTo[out,SubText[g,PrintIndices[c],l]];
    dd && AppendTo[out,SuperText[h,PrintIndices[d],l]];
    !((bb || cc || dd) && aa) && AppendTo[out,SubText[e,PrintIndices[a],l]];
    bb && AppendTo[out,SuperText[f,PrintIndices[b],l]];
    If[l,StringJoin,RowBox][out]]

PrintIndices[V_Integer,e_Integer,label:(_?BooleanQ):False] := PrintLabel[V,e,label]
PrintLabel[V_Integer,e_Integer,label_?BooleanQ,___] := SubText[pre[[1]],PrintIndices[ShiftIndices[V,e]],label]

PrintLabel[V_,e_Integer,label_?BooleanQ,vec_,cov_,duo_,dif_] := Module[
    {M = Supermanifold[V], nn,d,c,db},
    nn = Dims[M]; d = DiffVars[M]; c = DyadQ[V]; db = DiffMask[V];
    If[c < 0, Module[
        {es = BitAnd[e, Twiddle[BitOr[db[[1]],db[[2]]]]], n = (nn-2*d)/2, eps, par},
        eps = ShiftIndices[V,BitAnd[e, db[[1]]]]-(nn-2*d-Boole[InfinityQ[M]]-Boole[OriginQ[M]]);
        par = ShiftIndices[V,BitAnd[e, db[[2]]]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]]);
        PrintIndices[ShiftIndices[V,BitAnd[es, 2^n-1]],ShiftIndices[V,BitShiftLeft[es,n]],eps,par,label,vec,cov,duo,dif]],
      Module[{es = BitAnd[e, Twiddle[db]], eps},
        eps = ShiftIndices[V,BitAnd[e, db]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]]);
        If[!EmptyQ[eps],
            PrintIndices[ShiftIndices[V,es],{},If[c>0,{},eps],If[c>0,eps,{}],label,If[c>0,cov,vec],cov,If[c>0,dif,duo],dif],
            SubText[If[c>0,cov,vec],PrintIndices[ShiftIndices[V,es]],label]]]]]

IndexString[V_,d_] := PrintLabel[V,d,True,Sequence @@ pre]
IndexSymbol[V_,d_] := Symbol[IndexString[V,d]]
IndexSplit[B_] := Map[BitShiftLeft[1,#-1] &, Indices[B]]

OneQ[1] := True
OneQ[-1] := False
OneQ[0] := False
OneQ[x_] := x == 1
OneQ[True] := True
OneQ[False] := False

IndexParity[ind_List] := Module[{k = 1, t = false},
    While[k < Length[ind],
        If[ind[[k]] > ind[[k+1]],
            ind[[{k,k+1}]] = ind[[{k+1,k}]];
            t = !t; k ≠ 1 && (k -= 1),
            k += 1]];
    {t, ind}]
IndexParity[ind_List,s] := Module[{k = 1, t = false},
    While[k < Length[ind],
        If[ind[[k]] == ind[[k+1]],
            (ind[[k]] == 1 && InfinityQ[s] && Return[{t, ind, true}]);
            OneQ[s[[ind[[k]]]]] && (t = !t);
            Delete[ind,{k,k+1}],
        If[ind[[k]] > ind[[k+1]],
            ind[[k,k+1]] = ind[[k+1,k]];
            t = !t;
            k != 1 && (k -= 1),
            k += 1]]];
    {t, ind, false}]
