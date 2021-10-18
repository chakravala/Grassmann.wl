(* ::Package:: *)
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

(* Submanifold -> Submanifold *)
(* guide page: explain symbols, products
standard form, *)

(*
InterpretationBox[Selectable -> False]
SparseArray, Total(*behavior*)
SubmanifoldCoefficient
?SparseArray
Testing
Github workflow, pull requests
SetUsage
*)

<< GeneralUtilities`

ManifoldHeads = {MetricSignature,Submanifold}
ManifoldAlternatives = Alternatives @@ ManifoldHeads

GrassmannQ[_] := False
GrassmannQ[_MetricSignature] := True
GrassmannQ[_Submanifold] := True
GrassmannQ[_Multivector] := True
GrassmannQ[_Chain] := True
ManifoldQ[_] := False
ManifoldQ[ManifoldAlternatives[___]] := True
GradedQ[_] := False
GradedQ[_Chain] := True
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

Get["indices.wl"]
Get["directsum.wl"]
Get["generic.wl"]

(* basis *)

Labels[manifold_, prefix_String] := Labels[IndexBasis[Rank[manifold]],prefix]
Labels[manifold_, grade_, prefix_String:"v"] := Labels[IndexBasis[Rank[manifold],grade],prefix]
Labels[indices_List,prefix_String] := Map[Symbol[prefix <> StringJoin[Map[ToString, Indices[#]]]] &, indices]
GeometricAlgebraBasis[m_Submanifold] := GeometricAlgebraBasis[m,IndexBasis[Rank[m]]]
GeometricAlgebraBasis[m_Submanifold,grade_] := GeometricAlgebraBasis[m,IndexBasis[Rank[m],grade]]
GeometricAlgebraBasis[m_Submanifold,bits_List] := Map[Submanifold[m, CountOnes[#], #] &, bits]
GeometricAlgebraBasis[manifold_] := GeometricAlgebraBasis[Submanifold[manifold]]
AllocateBasis[manifold_] := AllocateBasis[Submanifold[manifold]]
AllocateBasis[m_Submanifold] := Set @@@ Transpose[{Unevaluated /@ Labels[m], GeometricAlgebraBasis[m]}]

GetBasis[V_, B_Integer] := Submanifold[V, CountOnes[B], B]

GZero[V_] := 0 GOne[V]
GOne[V_] := Submanifold[V, 0]

(* Chain *)

Chain /: SparseArray[Chain[_,_,a_SparseArray]] := a

Chain /: MakeBoxes[Chain[m_Submanifold,g_Integer,a_SparseArray],StandardForm] := Module[{n = Dims[m], t, indices, basis},
  t = SparseArray[a];
  indices = Flatten[t["ColumnIndices"]];
  basis = IndexBasis[n,g][[indices]];
  RowBox[Riffle[Map[RowBox[{t[[indices[[#]]]], PrintIndices[m, basis[[#]]]}] &, Range[Length[indices]]], "+"]]]

(* Multivector *)

Multivector /: Coefficient[Multivector[_,a_]] := a
Multivector /: SparseArray[Multivector[_,a_]] := SparseArray[Coefficient[a]]

Multivector[m_Multivector] := m
Multivector[Multivector[v_,a_SparseArray]] := Multivector[v,SparseArray[a]]

Multivector /: MakeBoxes[Multivector[m_Submanifold,a_SparseArray],StandardForm] := Module[{n = Dims[m], t},
  t = SparseArray[a];
  RowBox[Riffle[Map[RowBox[{t[[#]], PrintIndices[m, #-1]}] &,
    System`Convert`NotebookMLDump`UnorderedIntersection[IndexBasis[m]+1,Flatten[t["ColumnIndices"]]]], "+"]]]

Get["algebra.wl"]

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



Submanifold[x_,s:Submanifold[v_,g_,b_,y_]] := Submanifold[v,g,b,Times[x,y]]


