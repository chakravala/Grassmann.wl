
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

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
