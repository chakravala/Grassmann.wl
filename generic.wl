
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

Supermanifold[m_Integer] := m
Supermanifold[m_MetricSignature] := m
Supermanifold[Submanifold[m_, __]] := m
Parent[m_] := Manifold[m]

MetricProduct[v_,b_Integer] := MetricProduct[v,Indices[b]]
MetricProduct[v_,ind_List] := Times@@Map[BitSign,v[[ind]]]

MetricSignature /: Det[m_MetricSignature] := If[OddQ[CountOnes[Metric[m]]], -1, 1]
MetricSignature /: Abs[m_MetricSignature] := Sqrt[Abs[Det[m]]]
Submanifold /: Abs[m_Submanifold] := If[BasisQ[m], Sqrt[Reverse[m] m], Sqrt[Abs[Det[m]]]]

Bits[Submanifold[_, _, bits_, ___]] := bits
Rank[m_Integer] := m
Rank[m_List] := Length[m]
Rank[MetricSignature[dim_, ___]] := Rank[dim]
Rank[Submanifold[_, grade_, __]] := grade
Grade[m_?ManifoldQ] := Rank[m] - If[DyadicQ[m], 2, 1]*DiffVars[m]
Dims[m_] := Dims[Manifold[m]]
Dims[m_Integer] := m
Dims[m_List] := Length[m]
Dims[m_MetricSignature] := Rank[m]
Dims[Submanifold[_, grade_, __]] := grade
Dims[Submanifold[m_Submanifold, _, __]] := Dims[m]

RankList[m_Integer] := m
RankList[m_List] := m
RankList[MetricSignature[dim_, ___]] := RankList[dim]
RankList[Submanifold[_, grade_, __]] := grade
DimsList[m_] := Dims[Manifold[m]]
DimsList[m_Integer] := m
DimsList[m_List] := m
DimsList[m_MetricSignature] := RankList[m]
DimsList[Submanifold[_Integer, grade_, __]] := grade
DimsList[Submanifold[m_List, _, bits_, ___]] := m[[Indices[bits]]]
DimsList[Submanifold[MetricSignature[m_List,___], _, bits_, ___]] := m[[Indices[bits]]]
DimsList[Submanifold[m_Submanifold, _, __]] := DimsList[m]

(* options encoding *)

PolyQCalc[bits_Integer] := BitAnd[bits, 16] == 0
DyadQCalc[bits_Integer] := If[MemberQ[Range[8, 11], Mod[bits, 16]], -1,
  Boole[MemberQ[{4, 5, 6, 7}, Mod[bits, 16]]]]
InfinityQCalc[bits_Integer] := MemberQ[{1, 3, 5, 7, 9, 11}, Mod[bits, 16]]
OriginQCalc[bits_Integer] := MemberQ[{2, 3, 6, 7, 10, 11}, Mod[bits, 16]]

PolyQ[_Integer] := True
PolyQ[_List] := True
Map[(#[_Integer] := 0) &, {OptionsQ, DyadQ, DiffMode, DiffVars, Metric}]
Map[(#[_List] := 0) &, {OptionsQ, DyadQ, DiffMode, DiffVars, Metric}]
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
Metric[MetricSignature[_,_, bits_, ___]] := bits
Map[(#[_MetricSignature] := 0) &, {DiffMode, DiffVars, OptionsQ, Metric}]
Map[(#[Submanifold[m_, __]] := #[m]) &, {OptionsQ, Metric, PolyQ, DyadQ, DiffMode}]
DiffVars[Submanifold[m_, _, bits_, ___]] := ModuleScope[{dim,c} = {Dims[m], DiffMode[m]};
  Total[Map[Boole[MemberQ[Range[1+dim-If[c<0,2,1]*DiffVars[m],dim],#]] &,Indices[bits]]]]
(*Submanifold/:Basis[Times[m_Submanifold,__]]:=m*)

DyadicQ[t_] := DyadQ[Manifold[t]] < 0
DualQ[t_] := DyadQ[Manifold[t]] > 0
TangentSpaceQ[t_] := DiffVars[Manifold[t]] != 0

Map[(#[_Integer] := False) &, {DyadicQ, DualQ, TangentSpaceQ, InfinityQ, OriginQ}]
Map[(#[_List] := False) &, {DyadicQ, DualQ, TangentSpaceQ, InfinityQ, OriginQ}]

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
DiffMask[_List] := 0
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
    Origin2Q[m, a, b] && ! InfinityQ[m, a, b]};
  v = If[DyadicQ[m], BitOr[db[1], db[2]], db];
  (hi || ho) || (d != 0 &&
     CountOnes[BitAnd[a, v]] + CountOnes[BitAnd[b, v]] > DiffMode[m])]

ParityReverse[grade_] := OddQ[(grade-1)*grade/2]
ParityInvolute[grade_] := OddQ[grade]
ParityClifford[grade_] := Xor[ParityReverse[grade],ParityInvolute[grade]]
ParityConj = ParityReverse

GradeBasis[manifold_Integer,bits_] := BitAnd[bits,BitShiftLeft[1,manifold]-1]
GradeBasis[manifold_,bits_] := BitAnd[bits,BitShiftLeft[1,Grade[manifold]]-1]
Grade[manifold_,bits_] := CountOnes[GradeBasis[manifold,bits]]

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

GradeBasis[v,Submanifold[V_,_,B_,___]] := GradeBasis[V,B]
Grade[v,Submanifold[V_,_,B_,___]] := Grade[V,B]

Map[Module[{p = Symbol[StringJoin["Parity",ToString[#]]]},
  Submanifold /: #[b:Submanifold[V_,G_,B_,_]] := If[Coefficient[b]!=0,If[p[Grade[V,B]],Submanifold[-Coefficient[b],b],b],GZero[Manifold[b]]]] &
,{Reverse,Conjugate}]

Map[Module[{p = Symbol[StringJoin["Parity",ToString[#]]]},
  #[b:Submanifold[V_,G_,B_]] := If[Coefficient[b]!=0,If[p[Grade[V,B]],Submanifold[-Coefficient[b],b],b],GZero[Manifold[b]]]] &
,{Involute,Clifford}]
