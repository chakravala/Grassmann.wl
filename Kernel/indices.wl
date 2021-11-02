
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

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
printsep[_MetricSignature,_,_] := False
printsep[_Integer,_,_] := False
printsep[_List,_,_] := False
printsep[_,k_,n_] := k != n
sig[_Integer, _] := "x"(*"\[Times]"*)
sig[manifold_List, index_] := SubscriptBox["x",ToString[manifold[[index]]]]
sig[manifold_, index_] := manifold[[index]]
sig[manifold_MetricSignature, index_] := If[manifold[[index]], "-", "+"]
sig[manifold:Submanifold[m_List,___], index_] := SubscriptBox[manifold[[index]],ToString[m[[index]]]]
sig[manifold:MetricSignature[m_List,___], index_] := SubscriptBox[If[manifold[[index]], "-", "+"],ToString[m[[index]]]]

Prefixes[_] := pre
Prefixes[SubManifold[m_, __]] := Prefixes[m]
Prefixes[MetricSignature[_,_,_,_,_,prefix_List]] := prefix

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

ShiftIndices[_List,bits_Integer] := Indices[bits]
ShiftIndices[_List,indices:List[___Integer]] := indices

ShiftIndices[m_MetricSignature,bits_Integer] := ShiftIndices[m,Indices[bits,m]]
ShiftIndices[m:SubManifold[_,_,S_,___],b_Integer] := ShiftIndices[m,Indices[S,m][Indices[b]]]

PrintIndices[m_,bits_Integer,label:(_?BooleanQ):False] := PrintLabel[m,bits,label,Sequence @@ Prefixes[m]]

PrintIndex[index_Integer] := char[If[index>36, index-26, index]]
PrintIndex[index_] := ToString[index]
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

PrintIndices[m_List,bits_Integer,label:(_?BooleanQ):False] := PrintLabel[m,bits,label]
PrintLabel[m_List,bits_Integer,label_?BooleanQ,___] := SubText[pre[[1]],PrintIndices[ShiftIndices[m,bits]],label]

PrintLabel[V_,bits_Integer,label_?BooleanQ,vec_,cov_,duo_,dif_] := Module[{M, nn,d,c,db},
	{M,c,db} = {Supermanifold[V], DyadQ[V], DiffMask[V]}; {nn,d} = {Dims[M], DiffVars[M]};
    If[c < 0, Module[{n,es,eps,par}, {n,es,eps,par} = {(nn/2)-d,
          BitAnd[bits, Twiddle[BitOr@@db]],
          ShiftIndices[V,BitAnd[bits, db[[1]]]]-(nn-2*d-Boole[InfinityQ[M]]-Boole[OriginQ[M]]),
          ShiftIndices[V,BitAnd[bits, db[[2]]]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]])};
        PrintIndices[ShiftIndices[V,BitAnd[es, 2^n-1]],ShiftIndices[V,BitShiftRight[es,n]],eps,par,label,vec,cov,duo,dif]],
      Module[{es,eps}, {es,eps} = {BitAnd[bits, Twiddle[db]],
        ShiftIndices[V,BitAnd[bits, db]]-(nn-d-Boole[InfinityQ[M]]-Boole[OriginQ[M]])};
        If[!EmptyQ[eps],
            PrintIndices[ShiftIndices[V,es],{},If[c>0,{},eps],If[c>0,eps,{}],label,If[c>0,cov,vec],cov,If[c>0,dif,duo],dif],
            SubText[If[c>0,cov,vec],PrintIndices[ShiftIndices[V,es]],label]]]]]

IndexString[m_,bits_] := PrintIndices[m,bits,True]
IndexSymbol[m_,bits_] := Symbol[IndexString[m,bits]]
IndexSplit[bits_] := Map[BitShiftLeft[1,#-1] &, Indices[bits]]


IndexParity[indices_List] := ModuleScope[{k,t,ind} = {1, False, indices};
    While[k < Length[ind],
        If[ind[[k]] > ind[[k+1]],
            ind[[{k,k+1}]] = ind[[{k+1,k}]];
            t = !t; k ≠ 1 && (k -= 1),
            k += 1]];
    {t, ind}]
IndexParity[indices_List,m_] := ModuleScope[{k,t,ind} = {1, False, indices};
    While[k < Length[ind],
        If[ind[[k]] == ind[[k+1]],
            (ind[[k]] == 1 && InfinityQ[m] && Return[{t, ind, True}]);
            OneQ[m[[ind[[k]]]]] && (t = !t);
            Delete[ind,{k,k+1}],
        If[ind[[k]] > ind[[k+1]],
            ind[[k,k+1]] = ind[[k+1,k]];
            t = !t;
            k != 1 && (k -= 1),
            k += 1]]];
    {t, ind, False}]

(* parity *)

SymbolJoin[list__String] := Symbol[StringJoin[list]]
SymbolJoin[a_String,b_Symbol] := SymbolJoin[a,ToString[b]]
SymbolJoin[a_Symbol,b_] := SymbolJoin[ToString[a],b]

Map[Module[{p = SymbolJoin["Parity",#]},
  Submanifold /: #[b:Submanifold[V_,G_,B_,_]] := If[Coefficient[b]!=0,If[p[Grade[V,B]],Submanifold[-Coefficient[b],b],b],GZero[Manifold[b]]]] &
,{Reverse,Conjugate}]

Map[Module[{p = SymbolJoin["Parity",#]},
  #[b:Submanifold[V_,G_,B_]] := If[Coefficient[b]!=0,If[p[Grade[V,B]],Submanifold[-Coefficient[b],b],b],GZero[Manifold[b]]]] &
,{Involute,Clifford}]

(* complement parity *)

ParityRightHodge[manifold_Integer,bits_Integer,grade_,n_:Nothing] := Xor[OddQ[manifold],ParityRight[manifold,bits,grade,n]]
ParityLeftHodge[manifold_Integer,bits_Integer,grade_,n_] := Xor[OddQ[grade] && EvenQ[n], ParityRightHodge[manifold,bits,grade,n]]
ParityRightCalc[manifold_Integer,bits_Integer,grade_,n_:Nothing] := OddQ[bits+(grade+1)*grade/2]
ParityLeftCalc[manifold_Integer,bits_Integer,grade_,n_] := Xor[OddQ[grade] && EvenQ[n], ParityRight[manifold,bits,grade,n]]

Map[Module[{p = SymbolJoin["Parity",#], pg, pn, pc},
  {pc,pg,pn} = {SymbolJoin[p,"Calc"],SymbolJoin["Parity",#,"Hodge"],SymbolJoin["Parity",#,"Null"]};
  p[m_Integer,bits_Integer,n_Integer] := pc[0,Total[Indices[bits]],CountOnes[bits],n];
  pg[m_Integer,bits_Integer,n_Integer] := pg[CountOnes[BitAnd[m,bits]],Total[Indices[bits]],CountOnes[bits],n];
  pn[m_,bits_,v_] := If[ConformalQ[m] && CountOnes[BitAnd[bits,3]]==1, If[OddQ[bits],2*v,v/2],v];
  (*pg[m_Integer,bits_Integer] := pg[m,bits,CountOnes[bits]];
  pg[m_Integer,bits_Integer,grade_] := If[Xor[pc[0,Total[Indices[BitAnd[bits,BitShiftLeft[1,Dims[m]-DiffVars[m]]]-1]],grade,Dims[m]-DiffVars[m]],ConformalQ[m] && (BitAnd[bits,3]==2)],-1,1];*)
  p[V_Submanifold,B_] := p[V,B,CountOnes[B]];
  pg[V_Submanifold,B_] := pg[V,B,CountOnes[B]];
  p[V_Submanifold,B_,G_] := If[pc[0,Total[Indices[BitAnd[B,BitShiftLeft[1,Dims[V]-DiffVars[V]]-1]]],G,Dims[V]-DiffVars[v]],-1,1];
  pg[V_Submanifold,B_,G_] := Module[{dd = Dims[V]-DiffVars[V], ind, g},
    ind = Indices[BitAnd[B,BitShiftLeft[1,dd]-1]];
    g = MetricProduct[V,ind];
    If[Xor[pc[0,Total[ind],G,dd],ConformalQ[V] && (BitAnd[B,3] == 2)],-g,g]];
  p[Submanifold[V_,G_,B_,___]] := p[V,B,G];
  pg[Submanifold[V_,G_,B_,___]] := pg[V,B,G]] &,
{"Left","Right"}]

BitComplement[dim_Integer,bits_Integer,d_Integer:0,p_Integer:0] := Module[{up,nd,c},
    {up,nd} = {BitShiftLeft[1,If[p==1,0,p]-1], dim-d};
    c = BitOr[BitAnd[Twiddle[bits],BitXor[up,BitShiftLeft[1,nd]-1]],BitAnd[bits,BitXor[up,BitShiftLeft[BitShiftLeft[1,d]-1,nd]]]];
    If[CountOnes[BitAnd[c,up]]≠1, BitXor[c,up], c]]

(* parity *)

DigitsFast[b_,n_] := PadRight[Reverse[IntegerDigits[b,2]],n+1]

ParityJoin[n_,s_,a_,b_] := OddQ[Dot[DigitsFast[a,n],Accumulate[DigitsFast[BitShiftLeft[b,1],n]]]+CountOnes[BitAnd[BitAnd[a,b],s]]]

ConformalMask[v_] := 2^If[InfinityQ[v] && OriginQ[v],2,0]-1

ConformalCheck[v_,a_,b_] := Module[{bt=ConformalMask[v],i2o,o2i},
  {i2o,o2i} = {Infinity2OriginQ[v,a,b],Origin2InfinityQ[v,a,b]};
  {BitAnd[a,bt], BitAnd[b,bt], i2o, o2i, Xor[i2o,o2i]}]

ParityConformal[v_,a_,b_] := Module[{c,hio,cc,a3,b3,i2o,o2i,xor,pcc,bas},
  {c,hio} = {BitXor[a,b], InfinityOriginQ[v,a,b]};
  cc = hio || OriginInfinityQ[v,a,b];
  {a3,b3,i2o,o2i,xor} = ConformalCheck[v,a,b];
  {pcc,bas} = {Xor[xor,i2o,And[i2o,o2i]], If[xor,BitXor[BitOr[a3,b3],c],c]};
  {pcc, bas, cc, 0}]

(*ParityComplementInverse[n_,g_] := BitXor[ParityReverse[n-g],ParityReverse[g],OddQ[Binomial[n,2]]]*)

cga[v_,a_,b_] := (InfinityOriginQ[v,a,b] || OriginInfinityQ[v,a,b]) && (Vee[GetBasis[v,a],HodgeDual[GetBasis[v,b]]]==0)

ParityRegressive[v_Integer,a_,b_,skew_:False] := parityRegressive[v,a,b,skew]
parityRegressive[v_,a_,b_,skew_:False] := Module[{n,m,s,d,g,A,B,Q,Z,x,y,cc},
  {n,m,s} = {Dims[v],OptionsQ[v],Metric[v]};
  {d,g} = {DiffVars[v], If[IntegerQ[v], v, Grade[v]]};
  {A,B,Q,Z} = SymmetricMask[v,a,b];
  {x,y} = {BitComplement[n,A,d],BitComplement[n,B,d]};
  cc = skew && (InfinityOriginQ[v,A,y] || OriginInfinityQ[v,A,y]);
  If[((CountOnes[BitAnd[x,y]]==0) && (!DiffCheck[v,x,y])) || cc,
	Module[{c,l,bas,pcc,par},
      {c,l} = {BitXor[x,y], CountOnes[A]+CountOnes[B]};
      bas = BitComplement[n,c,d];
      {pcc,bas} = If[skew,Module[{a3,y3,i2o,o2i,xor,cx},
        {a3,y3,i2o,o2i,xor} = ConformalCheck[v,A,y];
        cx = cc || xor;
        {cx && Xor[Parity[v,a3,y3],i2o || o2i,And[xor,!i2o]], If[cx, BitXor[BitOr[a3,y3],bas],bas]}],
        {False,If[A+B!=0, bas, 0]}];
      par = Xor[ParityRight[s,A,n],ParityRight[s,B,n],ParityRight[s,c,n]];
      {Xor[OddQ[l*(l-g)],par,Parity[n,s,x,y],pcc], BitOr[bas,Q], True, Z}],
    {False,0,False,Z}]]

ParityRegressive[v_MetricSignature,a_,b_,skew_:False] := parityRegressive[v,a,b,skew]
ParityRegressive[v_,a_,b_] := Module[{p,c,t,z},{p,c,t,z} = ParityRegressive[MetricSignature[v],a,b]; {If[p,-1,1],c,t,z}]

ParityInterior[v_Integer,a_,b_] := Module[{A,B,Q,Z},
  {A,B,Q,Z} = SymmetricMask[v,a,b];
  If[DiffCheck[v,A,B] || cga[v,A,B],{False,0,False,Z},Module[{p,c,t,z},
    {p,c,t,z} = ParityRegressive[v,A,BitComplement[v,B,DiffVars[v]],True];
    {If[t, If[Xor[p,ParityRightCalc[0,Total[Indices[B]],CountOnes[B]]], -1, 1], 1], BitOr[c,Q], t, Z}]]]

ParityInterior[v_,a_,b_] := Module[{A,B,Q,Z,n},
  {A,B,Q,Z} = SymmetricMask[v,a,b]; n = Rank[v];
  If[DiffCheck[v,A,B] || cga[v,A,B],{False,0,False,Z},Module[{p,c,t,z,ind,g},
    {p,c,t,z} = ParityRegressive[MetricSignature[v],A,BitComplement[n,B,DiffVars[v]],True];
    ind = Indices[B]; g = MetricProduct[v,ind];
    {If[t, If[Xor[p,ParityRightCalc[0,Total[ind],CountOnes[B]]], -g, g], g], BitOr[c,Q], t, Z}]]]

ParityInner[v_Integer,a_,b_] := Module[{A,B,Q,Z},{A,B,Q,Z} = SymmetricMask[v,a,b]; If[Parity[v,A,B], -1, 1]]

ParityInner[v_,a_,b_] := Module[{A,B,Q,Z,g},
  {A,B,Q,Z} = SymmetricMask[v,a,b];
  g = Abs[Times@@Map[BitSign,v[[Indices[BitAnd[A,B]]]]]];
  If[Parity[MetricSignature[v],A,B], -g, g]]


Parity[n_,s_,a_,b_] := If[n>SparseLimit,ParityJoin[n,s,a,b],Parity[n,s,a,b]=ParityJoin[n,s,a,b]]
Parity[v_MetricSignature,a_Integer,b_Integer] := Module[{d=DiffMask[v],c}, c=FlipBits[Dims[v],If[DyadicQ[v],BitOr@@d,d]]; Parity[Dims[v],Metric[v],BitAnd[a,c],BitAnd[b,c]]]
Parity[v_Integer,a_Integer,b_Integer] := Parity[v,Metric[v],a,b]
Parity[v_,a_Integer,b_Integer] := Parity[MetricSignature[v],a,b]
Parity[Submanifold[v_,_,a_,_],Submanifold[v_,_,b_,_]] := Parity[v,a,b]
Conformal[Submanifold[m_,_,a_,_],Submanifold[m_,_,b_,_]] := Conformal[m,a,b]
Regressive[Submanifold[m_,_,a_,_],Submanifold[m_,_,b_,_]] := Regressive[m,a,b]
Interior[Submanifold[m_,_,a_,_],Submanifold[m_,_,b_,_]] := Interior[m,a,b]

Map[Module[{calc = SymbolJoin["Parity",#]},
  #[v_,a_,b_] := If[Dims[Supermanifold[v]] > SparseLimit,
    calc[v,a,b],#[v,a,b] = calc[v,a,b]];
  (*#[Submanifold[v_,_,b_,_],Submanifold[v_,_,c_,_]] := #[v,a,b];*)
] &, {Conformal,Regressive,Interior}]

