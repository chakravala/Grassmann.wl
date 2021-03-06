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

BeginPackage["Grassmann`"]

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
OneQ[_] := False
OneQ[x_?NumberQ] := x == 1
OneQ[True] := True
OneQ[False] := False

ZeroQ[0] := True
ZeroQ[1] := False
ZeroQ[_] := False
ZeroQ[x_?NumberQ] := x == 1
ZeroQ[False] := True
ZeroQ[True] := False

ZeroQ[Submanifold[_,_,_,x_]] := ZeroQ[x]
ZeroQ[t_Multivector|t_Chain] := ZeroQ[Norm[t]]
OneQ[t_Submanifold|t_Multivector|t_Chain] := Norm[t] == Coefficient[Scalar[t]] == 1

Parenthesis[x_Symbol] := ToBoxes[x,StandardForm]
Parenthesis[x_Times] := ToBoxes[x,StandardForm]
Parenthesis[x_?NumberQ] := ToBoxes[x,StandardForm]
Parenthesis[x_Submanifold] := ToBoxes[x,StandardForm]
Parenthesis[x_Multivector] := Sequence["(",ToBoxes[x,StandardForm],")"]
Parenthesis[x_] := Sequence["(",ToBoxes[x,StandardForm],")"]

Abs2[t_Multivector] := Module[{a=t.t},If[ScalarQ[a],Scalar[a],a]]
Abs2[t_Submanifold|t_Chain] := t.t
Submanifold /: Abs[t_Submanifold] := Sqrt[Abs2[t]]
Multivector /: Abs[t_Multivector] := Sqrt[Abs2[t]]
Chain /: Abs[t_Chain] := Sqrt[Abs2[t]]
Submanifold /: Norm[t_Submanifold] := Norm[Coefficient[t]]
Multivector /: Norm[t_Multivector] := Norm[Coefficient[t]]
Chain /: Norm[t_Chain] := Norm[Coefficient[t]]

ScalarQ[Submanifold[_,0,___]] := True
ScalarQ[_Submanifold] := False
ScalarQ[Chain[_,0,_]] := True
ScalarQ[_Chain] := False
ScalarQ[Multivector[_,coef_]] := ZeroQ[Norm[coef[[2;;-1]]]]

Scalar[t:Submanifold[_,0,___]] := t
Scalar[t:Chain[manifold_,0,coef_]] := Submanifold[manifold,0,0,coef[[1]]]
Scalar[Chain[manifold_,_,_]] := GZero[manifold]
Scalar[Submanifold[manifold_,___]] := GZero[manifold]
Scalar[Multivector[manifold_,coef_]] := Submanifold[manifold,0,0,coef[[1]]]

Submanifold /: Sqrt[Submanifold[v_,0_,b_,x_]] := Submanifold[v,0,b,Sqrt[x]]
Chain /: Sqrt[Chain[v_,0_,x_]] := Submanifold[v,0,b,Sqrt[x[[1]]]]

Get["Grassmann`indices`"]
Get["Grassmann`directsum`"]
Get["Grassmann`generic`"]

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
GetBasis[V_, B_Integer, x_] := Submanifold[V, CountOnes[B], B, x]
GetBasis[V_, Rule[B_Integer,x_]] := GetBasis[V,B-1,x]
GetBasis[V_, r__Rule] := Multivector[V,r]
GetBasis[V_, Nothing] := GetBasis[V]
GetBasis[V_] := GZero[V]

GZero[V_] := 0 GOne[V]
GOne[V_] := Submanifold[V, 0]

(* Chain *)

NormalMerge[r_] := Normal@Merge[r,Total]

Chain /: Coefficient[Chain[_, _,a_]] := a
Chain /: SparseArray[Chain[_,_,a_]] := SparseArray[a]

ChainToMulti[Chain[v_,g_,a_List]] := Map[Rule@@# &, Transpose@{IndexBasis[Dims[v], g],a}]
ChainToMulti[Chain[v_,g_,a_SparseArray]] := Map[Rule@@# &, Transpose@{IndexBasis[Dims@v, g][[a["ColumnIndices"]]],a["NonzeroValues"]}]

Chain[v_,g_,r__Rule] := Chain[v,g,{r}]
Chain[v_,g_,r:List[__Rule]] := Module[{n=Dims[v]},Chain[v,g,Normal@SparseArray[Map[Rule[BladeIndex[n,#[[1]]-1],#[[2]]] &,r],Binomial[n,g]]]]

ToChain[Submanifold[v_,g_,b_,x_]] := Chain[v,g,{b+1->x}]
ToChain[m_Chain] := m

Chain /: MakeBoxes[Chain[m_Submanifold,g_Integer,a_],StandardForm] := Module[{n = Dims[m], t, indices, basis},
  t = SparseArray@a;
  indices = Flatten[t["ColumnIndices"]];
  basis = IndexBasis[n,g][[indices]];
  RowBox[Riffle[Map[RowBox@{Parenthesis@t[[indices[[#]]]], PrintIndices[m, basis[[#]]]} &, Range@Length@indices], "+"]]]

(* Multivector *)

RuleShift[Rule[b_,x_]] := Rule[b+1,x]

Multivector /: Coefficient[Multivector[_,a_]] := a
Multivector /: SparseArray[m_Multivector] := SparseArray@Coefficient@m

ToMultivector[m_Multivector] := m
ToMultivector[Submanifold[v_,_,b_,x_]] := Multivector[v,b+1->x]
ToMultivector[m:Chain[v_,_,_]] := Multivector[v,RuleShift/@ChainToMulti[m]]
ToMultivector[Multivector[v_,a_SparseArray]] := Multivector[v,SparseArray[a]]

Multivector[v_,r:List[__Rule]] := Multivector[v,SparseArray[r,BitShiftLeft[1,Dims[v]]]]
Multivector[v_,r__Rule] := Multivector[v,{r}]

Multivector /: MakeBoxes[Multivector[m_Submanifold,a_],StandardForm] := Module[{t = SparseArray@a},
  RowBox[Riffle[Map[RowBox[{Parenthesis@t[[#]], PrintIndices[m, #-1]}] &,
    System`Convert`NotebookMLDump`UnorderedIntersection[IndexBasis[m]+1,Flatten@t["ColumnIndices"]]], "+"]]]

Get["Grassmann`algebra`"]

EndPackage[]
