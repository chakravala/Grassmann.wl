
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

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
