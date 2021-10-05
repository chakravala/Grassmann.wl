
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

(* indices cache *)

IndexLimit=20;SparseLimit=22;
CountOnes[bits_Integer]:=CountOnes[bits]=DigitCount[bits,2,1]
BinomialSum[n_Integer,m_Integer] :=
 BinomialSum[n,m] = If[m==0,0,BinomialSum[n,m-1]+Binomial[n,m-1]]
BinomialSum[dim_Integer] := Flatten[Table[BinomialSum[dim, grade], {grade, 0, dim}]]
Combinations[n_Integer,m_Integer]:=Combinations[n,m]=Subsets[Range[n],{m}]
Indices[bits_Integer]:=Flatten@Position[Reverse[IntegerDigits[bits,2]],1]
Indices[bits_Integer,_] := Indices[bits]
Indices[bits_Integer,v_List] := v[[Indices[bits]]]
Indices[bits_Integer,Submanifold[v_,___]] := Indices[bits,v]
Indices[bits_Integer,MetricSignature[v_,___]] := Indices[bits,v]
BladeIndexCalc[dim_Integer,bits_Integer]:=
 (Flatten@Position[Combinations[dim,CountOnes[bits]],Indices[bits]])[[1]]
BladeIndex[dim_Integer,bits_Integer]:=If[dim>20,BladeIndexCalc[bits,dim],
 BladeIndex[dim,bits]=BladeIndexCalc[dim,bits]]
BasisIndexCalc[dim_,bits_]:=BinomialSum[dim,CountOnes[bits]]+BladeIndex[dim,bits]
BasisIndex[dim_Integer,bits_Integer]:=If[dim>20,BasisIndexCalc[dim,bits],
 BasisIndex[dim,bits]=BasisIndexCalc[dim,bits]]
IndexToInteger[dim_Integer,indices_]:=FromDigits[Reverse[Table[Boole[MemberQ[indices,index]],{index,dim}]],2]
IndexToInteger[dim_List,indices_]:=FromDigits[Reverse[Map[Boole[MemberQ[indices,#]] &, dim]],2]
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

SignBit[x_] := Boole[Sign[x] < 0]
SignBit[True] := 0
SignBit[False] := 1

BitSign[x_] = x
BitSign[True] := -1
BitSign[False] := 1


