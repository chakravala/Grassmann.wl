(* ::Package:: *)
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

(* Submanifold -> Submanifold *)
(* guide page: explain symbols, products
standard form, *)

<< GeneralUtilities`

ManifoldHeads = {MetricSignature,Submanifold}
ManifoldAlternatives = Alternatives @@ ManifoldHeads

GrassmannQ[_] := False
GrassmannQ[_MetricSignature] := True
GrassmannQ[_Submanifold] := True
GrassmannQ[_Multivector] := True
ManifoldQ[_] := False
ManifoldQ[ManifoldAlternatives[___]] := True
GradedQ[_] := False
GradedQ[_Submanifold] := True
SubmanifoldQ[_] := False
SubmanifoldQ[_Submanifold] := True
MultivectorQ[_] := False
MultivectorQ[_Multivector] := True
BasisQ[_Submanifold] := False
BasisQ[_MetricSignature] := False
BasisQ[Submanifold[M_Submanifold, __]] := True

SymbolQ[_Symbol] := True
SymbolQ[_] := False

OneQ[1] := True
OneQ[-1] := False
OneQ[0] := False
OneQ[x_] := x == 1
OneQ[True] := True
OneQ[False] := False

(* indices cache *)

IndexLimit=20;SparseLimit=22;
CountOnes[bits_Integer]:=CountOnes[bits]=DigitCount[bits,2,1]
BinomialSum[n_Integer,m_Integer] :=
 BinomialSum[n,m] = If[m==0,0,BinomialSum[n,m-1]+Binomial[n,m-1]]
BinomialSum[dim_Integer] := Flatten[Table[BinomialSum[dim, grade], {grade, 0, dim}]]
Combinations[n_Integer,m_Integer]:=Combinations[n,m]=Subsets[Range[n],{m}]
Indices[bits_Integer]:=Flatten@Position[Reverse[IntegerDigits[bits,2]],1]
BladeIndexCalc[dim_Integer,bits_Integer]:=
 (Flatten@Position[Combinations[dim,CountOnes[bits]],Indices[bits]])[[1]]
BladeIndex[dim_Integer,bits_Integer]:=If[dim>20,BladeIndexCalc[bits,dim],
 BladeIndex[dim,bits]=BladeIndexCalc[dim,bits]]
BasisIndexCalc[dim_,bits_]:=BinomialSum[dim,CountOnes[bits]]+BladeIndex[dim,bits]
BasisIndex[dim_Integer,bits_Integer]:=If[dim>20,BasisIndexCalc[dim,bits],
 BasisIndex[dim,bits]=BasisIndexCalc[dim,bits]]
IndexToInteger[dim_Integer,indices_]:=FromDigits[Reverse[Table[Boole[MemberQ[indices,index]],{index,dim}]],2]
IndexBasisCalc[dim_Integer,grade_Integer]:=Map[IndexToInteger[dim,#]&,Combinations[dim,grade]]
IndexBasis[dim_Integer,grade_Integer]:=If[dim>SparseLimit,IndexBasisCalc[dim,grade],
 IndexBasis[dim,grade]=IndexBasisCalc[dim,grade]]
IndexBasis[dim_Integer] := Flatten[Table[IndexBasis[dim, grade], {grade, 0, dim}]]
IndexBasis[manifold_] := IndexBasis[Dims[manifold]]

BitAtIndex[bits_Integer, index_Integer] := BitAtIndex[bits, index] = Module[
 {mask = BitShiftLeft[1, index - 1]}, BitAnd[mask, bits] == mask]
BitAtIndex[bits_Integer, indices_] := Map[BitAtIndex[bits, #] &, indices]
doc2m[d_, o_, c_ : 0, q_ : 0] := doc2m[d,o,c,q] =
 BitOr[BitShiftLeft[1, d - 1], BitShiftLeft[1, 2 o - 1], 
  If[c < 0, 8, BitShiftLeft[1, 3 c - 1]], BitShiftLeft[1, 5 q - 1]]

(* Manifold *)

Manifold[manifold_MetricSignature] := manifold
Manifold[manifold_Submanifold] := manifold
Manifold[Submanifold[manifold_Submanifold, __]] := manifold
Manifold[Submanifold[manifold_Integer, __]] := manifold

MetricSignature /: Part[MetricSignature[___], index_] := BitAtIndex[0, index]
MetricSignature /: Part[MetricSignature[_, _, bits_, ___], index_] := BitAtIndex[bits, index]
(*MetricSignature[n_,o_:0,s_:0,v_:0]:=MetricSignature[n,o,s,v,0]*)

MetricSignature[s_String] := MetricSignature[StringLength[s],doc2m[Boole[StringContainsQ[s,vio[[1]]]],Boole[StringContainsQ[s,vio[[2]]]]],FromDigits[Reverse[Map[Boole[# == "-"] &, Characters[StringReplace[s, {vio[[1]] -> "+", vio[[2]] -> "-"}]]]], 2]]

Submanifold[signature_String] := Submanifold[MetricSignature[signature]]
Submanifold[manifold_] := Submanifold[manifold, Rank[manifold]]
Submanifold[manifold_,grade_Integer] := Submanifold[manifold, grade, BitShiftLeft[1, grade] - 1]
Submanifold[manifold_, indices_List] := Submanifold[manifold, Length[indices], IndexToInteger[Dims[manifold], indices]]
Submanifold[manifold_, 0] := Submanifold[manifold, 0 , 0]
Submanifold /: Part[Submanifold[_Integer, __], _Integer] := True
Submanifold /: Part[Submanifold[MetricSignature[_, _, bits_, ___], _, basis_, ___], index_] := BitAtIndex[bits, Indices[basis][[index]]]
Submanifold /: Part[Submanifold[Submanifold[_, _, bits_, ___], _, _], index_] := BitAtIndex[bits, index]
Submanifold /: Subscript[manifold_Submanifold, indices___] := manifold[indices]
Submanifold[manifold_, _, _][indices___] := Submanifold[manifold, {indices}]
(m:Submanifold[manifold_, _, _, coef_])[indices___] := Times[Submanifold[m, {indices}], coef]
Submanifold /: Times[t:Submanifold[manifold_, grade_, bits_], coef_] := Submanifold[manifold, grade, bits, coef]
Submanifold /: Times[t:Submanifold[manifold_, grade_, bits_, coef_], times_] := Submanifold[manifold, grade, bits, Times[coef,times]]
Submanifold /: Coefficient[Submanifold[_, _, _, coef_]] := coef
Submanifold /: Coefficient[Submanifold[_, _, _]] := 1
CoefficientQ[Submanifold[_, _, _, coef_]] := !OneQ[coef]
CoefficientQ[Submanifold[_, _, _]] := False

Supermanifold[m_Integer] := m
Supermanifold[m_MetricSignature] := m
Supermanifold[Submanifold[m_, __]] := m
Parent[m_] := Manifold[m]

MetricSignature /: Det[m_MetricSignature] := If[OddQ[CountOnes[Metric[m]]], -1, 1]
MetricSignature /: Abs[m_MetricSignature] := Sqrt[Abs[Det[m]]]
Submanifold /: Abs[m_Submanifold] := If[BasisQ[m], Sqrt[Reverse[m] m], Sqrt[Abs[Det[m]]]]

Indices[Submanifold[_, _, bits_, ___]] := Indices[bits]

Bits[Submanifold[_, _, bits_, ___]] := bits
Rank[m_Integer] := m
Rank[MetricSignature[dim_, ___]] := dim
Rank[Submanifold[_, grade_, __]] := grade
Grade[m_?ManifoldQ] := Rank[m] - If[DyadicQ[m], 2, 2]*DiffVars[m]
Dims[m_] := Dims[Manifold[m]]
Dims[m_Integer] := m
Dims[m_MetricSignature] := Rank[m]
Dims[Submanifold[_, grade_, __]] := grade
Dims[Submanifold[m_Submanifold, __]] := Dims[m]

Submanifold /: Rule[m_Submanifold] := Bits[m]+1->Coefficient[m]
Submanifold /: Rule[m_Submanifold, dim_] := BladeIndex[dim,Bits[m]]->Coefficient[m]

(* printing indices *)

vio = {"\[Infinity]", "\[EmptySet]"}
pre = {"v","w","\[PartialD]","\[Epsilon]"}
char[-1] := vio[[1]]
char[0] := vio[[2]]
char[n_Integer] := n
EmptyQ[set_] := Length[set] == 0
printsep[_, _MetricSignature, _, _] := Nothing
printsep[_, _Integer, _, _] := Nothing
printsep[out_, _, k_, n_] := k != n && AppendTo[out, ","]
sig[_Integer, _] := "x"(*"\[Times]"*)
sig[manifold_, index_] := manifold[[index]]
sig[manifold_MetricSignature, index_] := If[manifold[[index]], "-", "+"]

Prefixes[_] := pre
Prefixes[SubManifold[m_, __]] := Prefixes[m]
Prefixes[MetricSignature[_,_,_,_,_,prefix_List]] := prefix

MetricSignature[n_,m_,s_,f_,d_,v_String] := MetricSignature[n,m,s,f,d,{v,pre[[2]],pre[[3]],pre[[4]]}]

Labels[manifold_, prefix_String] := Labels[IndexBasis[Rank[manifold]],prefix]
Labels[manifold_, grade_, prefix_String:"v"] := Labels[IndexBasis[Rank[manifold],grade],prefix]
Labels[indices_List,prefix_String] := Map[Symbol[prefix <> StringJoin[Map[ToString, Indices[#]]]] &, indices]
GeometricAlgebraBasis[m_Submanifold] := GeometricAlgebraBasis[m,IndexBasis[Rank[m]]]
GeometricAlgebraBasis[m_Submanifold,grade_] := GeometricAlgebraBasis[m,IndexBasis[Rank[m],grade]]
GeometricAlgebraBasis[m_Submanifold,bits_List] := Map[Submanifold[m, CountOnes[#], #] &, bits]
GeometricAlgebraBasis[manifold_] := GeometricAlgebraBasis[Submanifold[manifold]]
AllocateBasis[manifold_] := AllocateBasis[Submanifold[manifold]]
AllocateBasis[m_Submanifold] := Set @@@ Transpose[{Unevaluated /@ Labels[m], GeometricAlgebraBasis[m]}]

(* display *)

MetricSignature /: MakeBoxes[s_MetricSignature, StandardForm] := Module[{dm,out,y,d,n},
 dm = DiffMode[s]; out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], If[SymbolQ[dm],MakeBoxes[dm],dm]],
    "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}]; y = DyadQ[s]; 
 {d,n} = {DiffVars[s], Dims[s] - If[d > 0, If[y < 0, 2 d, d], 0]};
 InfinityQ[s] && AppendTo[out, vio[[1]]]; 
 OriginQ[s] && AppendTo[out, vio[[2]]];
 d < 0 && AppendTo[out, SubscriptBox["", RowBox[Range[Abs[d], 1, -1]]]];
 out = Join[out, Map[If[#, "-", "+"] &, 
    s[[Range[Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], n]]]]];
 d > 0 && AppendTo[out, If[BitXor[Boole[y > 0], Boole[!PolyQ[s]]]>0, 
    SuperscriptBox["", RowBox[Range[1, Abs[d]]]],
    SubscriptBox["", RowBox[Range[1, Abs[d]]]]]];
 d > 0 && y < 0 && AppendTo[out, SuperscriptBox["", Range[1, Abs[d]]]];
 AppendTo[out, "\[RightAngleBracket]"];
 y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
 (*NamesIndex[s] > 1 && AppendTo[out, SubscriptBox["", subs[NamesIndex[s]]]];*)
 RowBox[out]]

Submanifold /: MakeBoxes[s_Submanifold, StandardForm] :=
 If[BasisQ[s], Module[{out = PrintIndices[Supermanifold[s],Bits[s]]},
  If[CoefficientQ[s],RowBox[{Coefficient[s],out}],out]],
  Module[{V,P,PnV,M,dm,out,y,d,dM,ind,n,nM},
    {V,dm} = {Supermanifold[s], DiffMode[s]}; P = If[IntegerQ[V], V, Parent[V]];
    PnV = P != V; M = If[PnV, Supermanifold[P], V];
    out = If[dm > 0, {SuperscriptBox[MakeBoxes[T], If[SymbolQ[dm],MakeBoxes[dm],dm]],
      "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}];
    PnV && PrependTo[out, SuperscriptBox["\[CapitalLambda]", Rank[V]]];
    {y,d,dM,ind} = {DyadQ[s], DiffVars[s], DiffVars[M], Indices[s]};
    {n,NM} = {Rank[s] - If[d > 0, If[y < 0, 2*d, d], 0],
      Dims[M] - If[dM > 0, If[y < 0, 2*dM, dM], 0]};
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
    (*NamesIndex[s] > 1 && AppendTo[out, SubscriptBox["", subs[NamesIndex[s]]]];*)
    PnV && AppendTo[out, "\[Times]" <> ToString[Length[V]]];
    RowBox[out]]]

(* options encoding *)

PolyQCalc[bits_Integer] := BitAnd[bits, 16] == 0
DyadQCalc[bits_Integer] := If[MemberQ[Range[8, 11], Mod[bits, 16]], -1,
  Boole[MemberQ[{4, 5, 6, 7}, Mod[bits, 16]]]]
InfinityQCalc[bits_Integer] := MemberQ[{1, 3, 5, 7, 9, 11}, Mod[bits, 16]]
OriginQCalc[bits_Integer] := MemberQ[{2, 3, 6, 7, 10, 11}, Mod[bits, 16]]

PolyQ[_Integer] := True
Map[(#[_Integer] := 0) &, {OptionsQ, DyadQ, DiffMode, DiffVars}]
Map[(#[t_] := #[Manifold[t]]) &, {OptionsQ, PolyQ, DyadQ, DiffMode, DiffVars}]
PolyQ[MetricSignature[_, bits_, ___]] := PolyQCalc[bits]
DyadQ[MetricSignature[_, bits_, ___]] := DyadQCalc[bits]
DiffMode[MetricSignature[_, _, _, _, d_]] := d
DiffVars[MetricSignature[_, _, _, diffvars_, ___]] := diffvars
MetricSignature /: Signature[MetricSignature[_, _, bits_, ___]] := bits
MetricSignature /: Signature[_MetricSignature] := 0
OptionsQ[MetricSignature[_, bits_, ___]] := bits
PolyQ[_MetricSignature] := PolyQCalc[0]
DyadQ[_MetricSignature] := DyadQCalc[0]
Map[(#[_MetricSignature] := 0) &, {DiffMode, DiffVars, OptionsQ, Metric}]
Map[(#[Submanifold[m_, __]] := #[m]) &, {OptionsQ, Metric, PolyQ, DyadQ, DiffMode}]
DiffVars[Submanifold[m_, _, bits_, ___]] := ModuleScope[{dim,c} = {Dims[m], DiffMode[m]};
  Total[Map[Boole[MemberQ[Range[1+dim-If[c<0,2,1]*DiffVars[m],dim],#]] &,Indices[bits]]]]
(*Submanifold/:Basis[Times[m_Submanifold,__]]:=m*)

DyadicQ[t_] := DyadQ[Manifold[t]] < 0
DualQ[t_] := DyadQ[Manifold[t]] > 0
TangentSpaceQ[t_] := DiffVars[Manifold[t]] != 0

Map[(#[_Integer] := False) &, {DyadicQ, DualQ, TangentSpaceQ, InfinityQ, OriginQ}]

Metric[manifold_, bits_Integer] := Times@@Map[Boole,manifold[[Indices[bits]]]]

InfinityQ[_MetricSignature] := InfinityQCalc[0]
InfinityQ[MetricSignature[_, bits_, ___]] := InfinityQCalc[bits]
InfinityQ[Submanifold[manifold_, _, bits_, ___]] := InfinityQ[manifold] && OddQ[bits]
(*InfinityQ[Times[m_Submanifold,__]]:=InfinityQ[m]*)

OriginQ[_MetricSignature] := OriginQCalc[0]
OriginQ[MetricSignature[_, bits_, ___]] := OriginQCalc[bits]
OriginQ[Submanifold[manifold_, _, bits_, ___]] :=
 OriginQ[manifold] && If[InfinityQ[manifold], BitAnd[2, bits] == 2, OddQ[bits]]
(*OriginQ[Times[m_Submanifold,__]]:=OriginQ[m]*)

(*isinf[m_Submanifold]:=InfinityQ[m]&&Grade[m]==1
isorigin[Submanifold[m_,grade_,_]]:=OriginQ[m]&&grade==1&&m[[InfiniftyQ[m]+1]]*)

ConformalQ[m_] := InfinityQ[m] && OriginQ[m]
OriginQ[m_, bits_Integer] := If[InfinityQ[m], BitAnd[2, bits] == 2, OddQ[bits]]
InfinityQ[m_, a_Integer, b_Integer] := ConformalQ[m] && (OddQ[a] || OddQ[b])
OriginQ[m_, a_Integer, b_Integer] := ConformalQ[m] && (OriginQ[m, a] || OriginQ[m, b])
Infinity2Q[m_, a_Integer, b_Integer] := ConformalQ[m] && OddQ[a] && OddQ[b]
Origin2Q[m_, a_Integer, b_Integer] := ConformalQ[m] && OriginQ[m, a] && OriginQ[m, b]
OriginInfinityQ[m_, a_Integer, b_Integer] :=
 ConformalQ[m] && OriginQ[m, a] && OddQ[b] && (! OriginQ[m, b]) && (! OddQ[a])
InfinityOriginQ[m_, a_Integer, b_Integer] :=
 ConformalQ[m] && OddQ[a] && OriginQ[m, b] && (! OddQ[b]) && (! OriginQ[m, a])
Infinity2OriginQ[m_, a_Integer, b_Integer] := Infinity2Q[m, a, b] && OriginQ[m, a, b]
Origin2InfinityQ[m_, a_Integer, b_Integer] := Origin2Q[m, a, b] && InfinityQ[m, a, b]

Twiddle[bits_Integer] := BitXor[bits, BitShiftLeft[1, 64] - 1]

DiffMask[_Integer] := 0
DiffMask[m_] := ModuleScope[{d,typemax} = {DiffVars[m], typemax = BitShiftLeft[1,64]-1};
  If[DyadicQ[m], Module[{v,w},
    {v,w} = {BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[m] - 2 d],
      BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[m] - d]};
    If[d < 0, {typemax - v, typemax - w}, {v, w}]],
   Module[{v = BitShiftLeft[BitShiftLeft[1, d] - 1, Dims[m] - d]},
   If[d < 0, typemax - v, v]]]]
SymmetricSplit[m_, bits_] := ModuleScope[{sm,dm} = {SymmetricMask[m,bits], DiffMask[m]};
  If[DyadicQ[m], {BitAnd[sm, dm[1]], BitAnd[sm, dm[2]]}, sm]]
SymmetricMask[m_, bits_] := Module[{d = DiffMask[m]},
  BitAnd[bits, If[DyadicQ[V], BitOr[d[[1]], d[[2]]], d]]]
SymmetricMask[m_, a_, b_] := Module[{d = DiffMask[m],dD,aD,bD},
  dD = If[DyadicQ[m], BitOr[d[[1]], d[[2]]], d];
  aD = BitAnd[a, dD]; bD = BitAnd[b, dD];
  {BitAnd[a, Twiddle[dD]], BitAnd[b, Twiddle[dD]], BitOr[aD, bD], BitAnd[aD, bD]}]
DiffCheck[m_, a_Integer, b_Integer] := Module[{d, db, v, hi, ho},
  {d, db, hi, ho} = {DiffVars[m], DiffMask[m],
    Infinity2Q[m, a, b] && ! OriginQ[m, a, b],
    Origin2Q[m, a, b] && ! InfinityQ[m, a, b]}
  v = If[DyadicQ[m], BitOr[db[1], db[2]], db];
  (hi || ho) || (d != 0 &&
     CountOnes[BitAnd[a, v]] + CountOnes[BitAnd[b, v]] > DiffMode[m])]

TangentSpace[m_MetricSignature,d_:1] := Module[{f=DiffVars[m]},TangentSpace[m,d,If[f!=0,f,1]]]
TangentSpace[m:MetricSignature[n:Repeated[_,{1,3}]],d_] := TangentSpace[m,d,1]
TangentSpace[m:MetricSignature[_,_,_,0,___],d_] := TangentSpace[m,d,1]
TangentSpace[m_MetricSignature,d_,f_] := MetricSignature[Rank[m]+If[DyadicQ[m], 2*f, f],OptionsQ[m],Signature[m],f,DiffMode[m]+d]
T = TangentSpace
TangentSpace /: Power[TangentSpace,mu_] := TangentSpace[mu]
TangentSpace /: Times[TangentSpace[mu_],m_] := TangentSpace[m,mu]

Subtangent[manifold_] := manifold[Range[Grade[manifold]+1,Dims[manifold]]]

FlipBits[dim_, bits_Integer] := BitAnd[2^dim - 1, Twiddle[bits]]

Dual[m_] := If[DyadicQ[m], m, Transpose[m]]
Dual[m_, b_] := Dual[m, b, Rank[m]/2]
Dual[m_, b_, m_] :=
 BitOr[BitAnd[BitShiftLeft[b, m], BitShiftLeft[1, Rank[m]]-1], BitShiftLeft[b, m]]

MetricSignature /: Transpose[m_MetricSignature] := Module[{c = DyadQ[m]},
 c < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 MetricSignature[Rank[m],
  doc2m[Boole[InfinityQ[m]], Boole[OriginQ[m]], If[c > 0, 0, 1]],
  FlipBits[Rank[m], Signature[m]], DiffVars[m], DiffMode[m]]]
Submanifold /: Transpose[Submanifold[m_, grade_, bits_]] := Module[{},
 DyadQ[m] < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 Submanifold[If[IntegerQ[m], Transpose[MetricSignature[m]], Transpose[m]], grade, bits]]
Submanifold /: Transpose[Submanifold[m_, grade_, bits_, coef_]] := Module[{},
 DyadQ[m] < 0 && Throw[domain];
 (*"$V is the direct sum of a vector space and its dual space"*)
 Submanifold[If[IntegerQ[m], Transpose[MetricSignature[m]], Transpose[m]], grade, bits, coef]]

(* printing indices *)

IndexText[v_, indices_] := v <> StringJoin[ToString /@ indices]
SubText[v_, indices_, True] := IndexText[v, indices]
SubText[v_, index_, False] := SubscriptBox[v, index]
SubText[v_, indices_List, False] := SubscriptBox[v, RowBox[Riffle[indices, ","]]]
SuperText[v_, indices_, True] := IndexText[v, indices]
SuperText[v_, indices_, False] := SuperscriptBox[v, RowBox[Riffle[indices, ","]]]

ShiftIndices[m_, bits_Integer] := ShiftIndices[Supermanifold[m], bits]
ShiftIndices[m_, list:List[___]] := Module[{M = Supermanifold[m], set = list},
    !EmptyQ[set] && Module[{k = 1, n = Length[set]},
        InfinityQ[M] && set[[1]] == 1 && (set[[1]] = -1; k += 1);
        shift = Boole[InfinityQ[M]] + Boole[OriginQ[M]];
        OriginQ[M] && n>=k && set[[k]]==shift && (set[[k]] = 0;k+=1);
        shift > 0 && (set[[k;;n]] -= shift)];set]

ShiftIndices[_Integer,bits_Integer] := Indices[bits]
ShiftIndices[_Integer,indices:List[___Integer]] := indices

ShiftIndices[m_MetricSignature,bits_Integer] := ShiftIndices[m,Indices[bits]]
ShiftIndices[m:SubManifold[_,_,S_,___],b_Integer] := ShiftIndices[m,Indices[S][Indices[b]]]

PrintIndices[m_,bits_Integer,label:(_?BooleanQ):False] := PrintLabel[m,bits,label,Sequence @@ Prefixes[m]]

PrintIndex[index_] := char[If[index>36, index-26, index]]
PrintIndices[bits_Integer] := PrintIndices[Indices[bits]]
PrintIndices[indices_List] := Map[PrintIndex, indices]
PrintIndices[a_,b_,l:(_?BooleanQ):False,e:(_String):pre[[1]],f:(_String):pre[[2]]] := PrintIndices[a,b,{},{},l,e,f]
PrintIndices[a_,b_,c_,d_,l:(_?BooleanQ):False,e:(_String):pre[[1]],f:(_String):pre[[2]],g:(_String):pre[[3]],h:(_String):pre[[4]]] := ModuleScope[
    {aa,bb,cc,dd,out} = {EmptyQ[a], !EmptyQ[b], !EmptyQ[c], !EmptyQ[d], {}};
    cc && AppendTo[out,SubText[g,PrintIndices[c],l]];
    dd && AppendTo[out,SuperText[h,PrintIndices[d],l]];
    !((bb || cc || dd) && aa) && AppendTo[out,SubText[e,PrintIndices[a],l]];
    bb && AppendTo[out,SuperText[f,PrintIndices[b],l]];
    If[l,StringJoin,RowBox][out]]

PrintIndices[m_Integer,bits_Integer,label:(_?BooleanQ):False] := PrintLabel[m,bits,label]
PrintLabel[m_Integer,bits_Integer,label_?BooleanQ,___] := SubText[pre[[1]],PrintIndices[ShiftIndices[m,bits]],label]

PrintLabel[V_,bits_Integer,label_?BooleanQ,vec_,cov_,duo_,dif_] := Module[{M, nn,d,c,db},
	{M,c,db} = {Supermanifold[V], DyadQ[V], DiffMask[V]}; {nn,d} = {Dims[M], DiffVars[M]};
    If[c < 0, Module[{n,es,eps,par}, {n,es,eps,par} = {(nn-2*d)/2,
          BitAnd[bits, Twiddle[BitOr[db[[1]],db[[2]]]]],
          ShiftIndices[V,BitAnd[bits, db[[1]]]]-(nn-2*d-Boole[InfinityQ[M]]-Boole[OriginQ[M]]),
          ShiftIndices[V,BitAnd[bits, db[[2]]]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]])};
        PrintIndices[ShiftIndices[V,BitAnd[es, 2^n-1]],ShiftIndices[V,BitShiftLeft[es,n]],eps,par,label,vec,cov,duo,dif]],
      Module[{es,eps}, {es,eps} = {BitAnd[bits, Twiddle[db]],
        ShiftIndices[V,BitAnd[bits, db]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]])};
        If[!EmptyQ[eps],
            PrintIndices[ShiftIndices[V,es],{},If[c>0,{},eps],If[c>0,eps,{}],label,If[c>0,cov,vec],cov,If[c>0,dif,duo],dif],
            SubText[If[c>0,cov,vec],PrintIndices[ShiftIndices[V,es]],label]]]]]

IndexString[m_,bits_] := PrintIndices[m,bits,True]
IndexSymbol[m_,bits_] := Symbol[IndexString[m,bits]]
IndexSplit[bits_] := Map[BitShiftLeft[1,#-1] &, Indices[bits]]

(* operations *)

IndexParity[indices_List] := ModuleScope[{k,t} = {1, False};
    While[k < Length[indices],
        If[indices[[k]] > indices[[k+1]],
            indices[[{k,k+1}]] = indices[[{k+1,k}]];
            t = !t; k ≠ 1 && (k -= 1),
            k += 1]];
    {t, indices}]
IndexParity[indices_List,m] := ModuleScope[{k,t} = {1, False};
    While[k < Length[indices],
        If[indices[[k]] == indices[[k+1]],
            (indices[[k]] == 1 && InfinityQ[m] && Return[{t, indices, true}]);
            OneQ[m[[indices[[k]]]]] && (t = !t);
            Delete[indices,{k,k+1}],
        If[indices[[k]] > indices[[k+1]],
            indices[[k,k+1]] = indices[[k+1,k]];
            t = !t;
            k != 1 && (k -= 1),
            k += 1]]];
    {t, indices, false}]

ParityReverse[grade_] := OddQ[(grade-1)/2]
ParityInvolute[grade_] := OddQ[grade]
ParityClifford[grade_] := Xor[ParityReverse[grade],ParityInvolute[grade]]
ParityConj = ParityReverse

GradeBasis[manifold_Integer,bits_] := BitAnd[bits,BitShiftLeft[1,manifold]-1]
GradeBasis[manifold_,bits_] := BitAnd[bits,BitShiftLeft[1,Grade[manifold]]-1]
Grade[manifold_,bits_] := CountOnes[GradeBasis[manifold,bits]]

Mixed[m_, ibk_Integer] := ModuleScope[{n,d,mc} = {Dims[m], DiffVars[m], DualQ[m]};
    If[d != 0,Module[{
        {a,b} = {BitAnd[ibk,BitShifLeft[1,n-d]-1],BitAnd[ibk,DiffMask[m]]}},
        If[mc,BitOr[BitShiftLeft[a,n-d],BitShiftLeft[b,n]],BitOr[a,BitShiftLeft[b,n-d]]]],
        If[vc, BitShiftLeft[ibk, n, ibk]]]]

Combine[v_,w_,a_Integer,b_Integer] := If[DualQ[v]!=DualQ[w],
    Throw[error](*"$v and $w incompatible"*),
    {V,W} = {Supermanifold[v],Supermanifold[w]};
    If[TangentSpaceQ[V]||TangentSpaceQ[W],
        {gV,gW} = {If[IntegerQ[V],V,Grade[V]],If[IntegerQ[W],W,Grade[W]]};
        {gras1,gras2} = {BitAnd[a,BitShiftLeft[1,gV]-1],BitAnd[b,BitShiftLeft[1,gW]-1]};
        diffs = BitOr[BitAnd[a,DiffMask[W]],BitAnd[b,DiffMask[W]]];
        BitOr[gras1,BitShiftLeft[gras2,gV],BitShiftLeft[diffs,Dims[W]]] (* BitOr[A,BitShiftLeft[B,N-D]] *)
    ,
        BitOr[iak,BitShiftLeft[ibk,Dims[V]]]]] (* ibk *)

(* complement parity *)

ParityRightHodge[manifold_Integer,bits_Integer,grade_,n_:Nothing] := Xor[OddQ[manifold],ParityRight[manifold,bits,grade,n]]
ParityLeftHodge[manifold_Integer,bits_Integer,grade_,n_] := Xor[OddQ[grade] && EvenQ[n], ParityRightHodge[manifold,bits,grade,n]]
ParityRight[manifold_Integer,bits_Integer,grade_,n_:Nothing] := OddQ[bits+(grade+1)*grade/2]
ParityLeft[manifold_Integer,bits_Integer,grade_,n_] := Xor[OddQ[grade] && EvenQ[n], ParityRight[manifold,bits,grade,n]]

Map[Module[{p = Symbol[StringJoin["Parity",#]], pg, pn},
  {pg,pn} = {Symbol[StringJoin["Parity",#,"Hodge"]],Symbol[StringJoin["Parity",#,"Null"]]};
  p[m_Integer,bits_Integer,n_Integer] := p[0,Total[Indices[bits]],CountOnes[bits],n];
  pg[m_Integer,bits_Integer,n_Integer] := pg[CountOnes[BitAnd[m,bits]],Total[Indices[bits]],CountOnes[bits],n];
  pn[m_,bits_,v_] := If[ConformalQ[m] && CountOnes[BitAnd[bits,3]]==1, If[OddQ[bits],2*v,v/2],v];
  pg[m_Integer,bits_Integer,grade:CountOnes[bits]] := If[Xor[p[0,Total[Indices[BitAnd[bits,BitShiftLeft[1,Dims[m]-DiffVars[m]]-1]]],grade,Dims[m]-DiffVars[m]],ConformalQ[m] && (BitAnd[bits,3]==2)],-1,1]] &,{"Left","Right"}]
 
BitComplement[dim_Integer,bits_Integer,d:Integer:0,p:Integer:0] := Module[{up,nd,c},
    {up,nd} = {BitShiftLeft[1,If[p==1,0,p]-1], dim-d};
    c = BitOr[BitAnd[Twiddle[bits],BitXor[up,BitShiftLeft[1,nd]-1]],BitAnd[bits,BitXor[up,BitShiftLeft[BitShiftLeft[1,d]-1,nd]]]]
    If[CountOnes[BitAnd[c,up]]≠1, BitXor[c,up], c]]

(* set theory ∪,∩,⊆,⊇ *)

Map[(# /: Union[x:#] := x) &, ManifoldHeads]
Map[(# /: Union[a:#,b_?ManifoldQ,c__?ManifoldQ] := Union[Union[a,b],c]) &, ManifoldHeads]

Map[(# /: Intersection[x:#] := x) &, ManifoldHeads]
Map[(# /: Intersection[a:#,b_?ManifoldQ,c__?ManifoldQ] := Intersection[Intersection[a,b],c]) &, ManifoldHeads]

OptionsList[m_] := {InfinityQ[m], OriginQ[m], DyadQ[m], PolyQ[m]}
CombineOptions[a_,b_] := ModuleScope[
  {ds,list} = {(Rank[a]==Rank[b])&&(Signature[a]==Signature[b]),
    Map[If[IntegerQ[#],#,Boole[#]]&,Join[Drop[OptionsList[a],-1], Drop[OptionsList[b],-1]]]};
  If[list == {0,0,0,0,0,0},doc2m[0,0,0],
    If[list == {0,0,1,0,0,1},doc2m[0,0,1],
      If[list == {0,0,0,0,0,1},doc2m[0,0,If[ds,-1,0]],
        If[list == {0,0,1,0,0,0},doc2m[0,0,If[ds,-1,0]],
          Throw[domain]]]]]]

CirclePlus[a_MetricSignature, b_MetricSignature] := Module[{n,nm,x,y,list,option},
  {n,nm,x,y,list} = {Rank[a], nm = Rank[a]==Rank[b], x = Signature[a], y = Signature[b],
  list = Map[If[IntegerQ[#],#,Boole[#]]&,Join[Drop[OptionsList[a],-1], Drop[OptionsList[b],-1]]]};
  option = If[list == {0,0,0,0,0,0},doc2m[0,0,0],
    If[list == {0,0,1,0,0,1},doc2m[0,0,1],
      If[list == {0,0,0,0,0,1},doc2m[0,0,If[nm,If[y!=FlipBits[n,x],0,-1],0]],
        If[list == {0,0,1,0,0,0},doc2m[0,0,If[nm,If[x!=FlipBits[n,y],0,-1],0]],
          Throw[domain]]]]];
  MetricSignature[n+Rank[b],option,BitOr[x,BitShiftLeft[y,n]],Max[DiffVars[a],DiffVars[b]],Max[DiffMode[a],DiffMode[b]]]]

CirclePlus[Submanifold[v_,n_,x_,___],Submanifold[w_,m_,y_,___]] := Module[{b=IntegerQ[w],
    z = If[(DualQ[v]==DualQ[w])||(v!=w^T), Combine[v,w,x,y],BitOr[Mixed[v,x],Mixed[w,u]]]},
    Submanifold[If[IntegerQ[v], If[b, v+w, CirclePlus[MetricSignature[v],w]], If[b, CirclePlus[v,MetricSignature[W]], CirclePlus[v,w]]],CountOnes[Z],Z]]

V0 = MetricSignature[0]
\[DoubleStruckCapitalR] = MetricSignature[1]

Map[(MetricSignature /: Power[m:MetricSignature[_,#,___],i_Integer] := If[i==0,Return[V0],Nest[CirclePlus[m,#] &, m, i-1]]) &, Range[0,4]]
MetricSignature /: Power[MetricSignature[n_],i_Integer] := MetricSignature[n*i]

(* conversions *)

Manifold[m_Submanifold] := m
Manifold[Submanifold[m_Integer, __]] := m
Manifold[Submanifold[m_Submanifold, __]] := m
(*MetricSignature[m:Submanifold[_,n_,_]] = MetricSignature[N,OptionsQ[m]](Vector(signbit.(V[:])),DiffVars[m],DiffMode[m])*)

(* Chain *)

Chain /: SparseArray[Chain[_,_,a_]] := a

Chain /: MakeBoxes[Chain[m_Submanifold,g_Integer,a_SparseArray],StandardForm] := Module[{n = Dims[m], t, indices, basis},
  t = SparseArray[a];
  indices = Flatten[t["ColumnIndices"]];
  basis = IndexBasis[n,g][[indices]];
  RowBox[Riffle[Map[RowBox[{t[[indices[[#]]]], PrintIndices[m, basis[[#]]]}] &, Range[Length[indices]]], "+"]]]

(* Multivector *)

Multivector /: SparseArray[Multivector[_,a_]] := a

Multivector /: MakeBoxes[Multivector[m_Submanifold,a_SparseArray],StandardForm] := Module[{n = Dims[m], t},
  t = SparseArray[a];
  RowBox[Riffle[Map[RowBox[{t[[#]], PrintIndices[m, #-1]}] &,
    System`Convert`NotebookMLDump`UnorderedIntersection[IndexBasis[m]+1,Flatten[t["ColumnIndices"]]]], "+"]]]

(* algebra *)

Submanifold /: Minus[m_Submanifold] := Times[m,-1]
Submanifold /: Minus[a:Submanifold[m_, __],b:Submanifold[m_, __]] := Plus[a,Minus[b]]

Submanifold[m_, g_, b_] := Submanifold[m, g, b, 1]

Plus[a:Submanifold[m_, g_, b_, _], b:Submanifold[m_, g_, b_, _]]

(*Submanifold /: Plus[t:Submanifold[m_, g_, b_, 1]..] := Times[{t}[[1]],Length[{t}]]*)
Submanifold /: Plus[t:Submanifold[m_, g_, b_, _]..] := Times[{t}[[1]],Total[Map[Coefficient,{t}]]]
Submanifold /: Plus[t:Submanifold[m_, g_ ,_, _]..] := Module[{n=Dims[m]},Chain[m,g,SparseArray[Normal@Merge[Map[Rule[#,n] &, {t}],Total],Binomial[n,g]]]]
Submanifold /: Plus[t:Submanifold[m_, _, _, _]..] := Multivector[m,SparseArray[Normal@Merge[Map[Rule, {t}],Total],BitShiftLeft[1,Dims[m]],Total]]

(*UpValues[Submanifold] = Join[UpValues[Submanifold],{
	HoldPattern[Plus[t:Submanifold[m_, g_, b_, _]..] :> Times[{t}[[1]],Total[Map[Coefficient,{t}]]]],
	HoldPattern[Plus[t:Submanifold[m_, g_ ,_, _]..] :> Module[{n=Dims[m]},Chain[m,g,SparseArray[Normal@Merge[Map[Rule[#,n] &, {t}],Total],Binomial[n,g]]]]],
	HoldPattern[Plus[t:Submanifold[m_, _, _, _]..] :> Multivector[m,SparseArray[Normal@Merge[Map[Rule, {t}],Total],BitShiftLeft[1,Dims[m]],Total]]]}];
UpValues[Submanifold] = SubsetMap[Reverse, UpValues[Submanifold], -3 ;; -1];*)

Chain /: Plus[t:Chain[m_,g_,_]..] := Chain[m,g,Total[Map[SparseArray,{t}]]]
Multivector /: Plus[t:Multivector[m_,_]..] := Multivector[m,Total[Map[SparseArray,{t}]]]

Chain /: Minus[Chain[m_, g_, a_]] := Chain[m, g, -a]
Chain /: Minus[Chain[m_, g_, x_], Chain[m_, g_, y_]] := Chain[m, g, x - y]
Multivector /: Minus[Multivector[m_, a_]] := Multivector[m, -a]
Multivector /: Minus[Multivector[m_, x_], Multivector[m_, y_]] := Multivector[m, x - y]

