
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

(* Manifold *)

Manifold[manifold_MetricSignature] := manifold
Manifold[manifold_Submanifold] := manifold
Manifold[Submanifold[manifold_Submanifold, __]] := manifold
Manifold[Submanifold[manifold_Integer, __]] := manifold
Manifold[Submanifold[manifold_Symbol, __]] := manifold

MetricSignatureQ[_] := False
MetricSignatureQ[_MetricSignature] := True
MetricSignature /: Part[MetricSignature[___], index_] := BitAtIndex[0, index]
MetricSignature /: Part[MetricSignature[_, _, bits_, ___], index_] := BitAtIndex[bits, index]
(*MetricSignature[n_,o_:0,s_:0,v_:0]:=MetricSignature[n,o,s,v,0]*)

MetricSignature[v:Submanifold[_,n_,__]] := MetricSignature[n,OptionsQ[v],FromDigits[Reverse[Map[SignBit[v[[#]]] &, Range[n]]],2],DiffVars[v],DiffMode[v]]
MetricSignature[s_String] := MetricSignature[StringLength[s],doc2m[Boole[StringContainsQ[s,vio[[1]]]],Boole[StringContainsQ[s,vio[[2]]]]],FromDigits[Reverse[Map[Boole[# == "-"] &, Characters[StringReplace[s, {vio[[1]] -> "+", vio[[2]] -> "-"}]]]], 2]]
MetricSignature[n_,m_,s_,f_,d_,v_String] := MetricSignature[n,m,s,f,d,{v,pre[[2]],pre[[3]],pre[[4]]}]

Submanifold[signature_String] := Submanifold[MetricSignature[signature]]
Submanifold[manifold_] := Submanifold[manifold, Rank[manifold]]
Submanifold[manifold_Symbol] := Submanifold[manifold, manifold]
Submanifold[manifold_,grade_Symbol] := Submanifold[manifold, grade, PseudoList[n]]
Submanifold[manifold_,grade_Integer] := Submanifold[manifold, grade, BitShiftLeft[1, grade] - 1]
Submanifold[manifold_, indices_List, c_:1] := If[Length[Union[indices]]!=Length[indices],
  GZero[manifold],
  Submanifold[manifold, Length[indices], IndexToInteger[DimsList[manifold], indices],
    If[IndexParity[Flatten[Map[Position[DimsList[manifold],#]&,indices]]][[1]],-c,c]]]
Submanifold[manifold_, 0] := Submanifold[manifold, 0 , 0]
Submanifold /: Part[Submanifold[_Integer, __], _Integer] := 1
Submanifold /: Part[Submanifold[_List, __], _Integer] := 1
Submanifold /: Part[Submanifold[_Integer, __], l_List] := ConstantArray[1,Length[l]]
Submanifold /: Part[Submanifold[_List, __],  _List] := ConstantArray[1,Length[l]]
Submanifold /: Part[Submanifold[MetricSignature[_, _, bits_, ___], _, basis_, ___], index_] := BitSign[BitAtIndex[bits, Indices[basis][[index]]]]
Submanifold /: Part[Submanifold[MetricSignature[_], _, basis_, ___], index_] := BitSign[BitAtIndex[0, Indices[basis][[index]]]]
Submanifold /: Part[Submanifold[MetricSignature[_,_], _, basis_, ___], index_] := BitSign[BitAtIndex[0, Indices[basis][[index]]]]
Submanifold /: Part[Submanifold[Submanifold[_, _, bits_, ___], _, _], index_] := BitSign[BitAtIndex[bits, index]]
Submanifold /: Subscript[manifold_Submanifold, indices___] := manifold[indices]
Submanifold[manifold_, _, _][indices___] := Submanifold[manifold, {indices}]
Submanifold[manifold_, _, _, coef_][indices___] := Submanifold[manifold, {indices}, coef]
Submanifold /: Times[t:Submanifold[manifold_, grade_, bits_], coef_] := Submanifold[manifold, grade, bits, coef]
Submanifold /: Times[t:Submanifold[manifold_, grade_, bits_, coef_], times_] := Submanifold[manifold, grade, bits, Times[coef,times]]
Submanifold /: Coefficient[Submanifold[_, _, _, coef_]] := coef
Submanifold /: Coefficient[Submanifold[_, _, _]] := 1
CoefficientQ[Submanifold[_, _, _, coef_]] := !OneQ[coef]
CoefficientQ[Submanifold[_, _, _]] := False

Indices[Submanifold[_, _, bits_, ___]] := Indices[bits]

Submanifold /: Rule[m_Submanifold] := Bits[m]+1->Coefficient[m]
Submanifold /: Rule[m_Submanifold, dim_] := BladeIndex[dim,Bits[m]]->Coefficient[m]

SupermanifoldQ[V_] := IntegerQ[V] || ListQ[V]

(* display *)

MetricSignature /: MakeBoxes[s_MetricSignature, StandardForm] := Module[{dm,out,y,d,n},
 dm = DiffMode[s]; out = If[dm > 0, {SuperscriptBox["T", If[SymbolQ[dm],ToBoxes[dm,StandardForm],dm]],
    "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}]; y = DyadQ[s]; 
 {d,n} = {DiffVars[s], Dims[s] - If[d > 0, If[y < 0, 2 d, d], 0]};
 InfinityQ[s] && AppendTo[out, vio[[1]]]; 
 OriginQ[s] && AppendTo[out, vio[[2]]];
 d < 0 && AppendTo[out, SubscriptBox["", Range[Abs[d], 1, -1]]];
 out = Join[out, Map[sig[s,#] &,
    Range[Boole[InfinityQ[s]] + Boole[OriginQ[s]] + 1 + If[d < 0, Abs[d], 0], n]]];
 d > 0 && AppendTo[out, If[BitXor[Boole[y > 0], Boole[!PolyQ[s]]]>0, 
    SuperscriptBox["", RowBox[Range[1, Abs[d]]]],
    SubscriptBox["", RowBox[Range[1, Abs[d]]]]]];
 d > 0 && y < 0 && AppendTo[out, SuperscriptBox["", RowBox[Range[1, Abs[d]]]]];
 AppendTo[out, "\[RightAngleBracket]"];
 y != 0 && AppendTo[out, If[y < 0, "*", "\[Transpose]"]];
 (*NamesIndex[s] > 1 && AppendTo[out, SubscriptBox["", subs[NamesIndex[s]]]];*)
 RowBox[out]]

(*Submanifold /: MakeBoxes[s_Submanifold, StandardForm] := MakeBoxes[Coefficient[s],StandardForm]*)

Submanifold /: MakeBoxes[s_Submanifold, StandardForm] :=
 If[BasisQ[s], Module[{out = PrintIndices[Supermanifold[s],Bits[s]]},
  If[CoefficientQ[s],RowBox[{Parenthesis[Coefficient[s]],out}],out]],
  Module[{V,P,PnV,M,dm,out,y,d,dM,ind,n,nM},
    {V,dm} = {Supermanifold[s], DiffMode[s]}; P = If[SupermanifoldQ[V], V, Parent[V]];
    PnV = P != V; M = If[PnV, Supermanifold[P], V];
    out = If[dm > 0, {SuperscriptBox["T", If[SymbolQ[dm],ToBoxes[dm,StandardForm],dm]],
      "\[LeftAngleBracket]"}, {"\[LeftAngleBracket]"}];
    PnV && PrependTo[out, SuperscriptBox["\[CapitalLambda]", Rank[V]]];
    {y,d,dM,ind} = {DyadQ[s], DiffVars[s], DiffVars[M], Indices[s]};
    {n,NM} = {Rank[s] - If[d > 0, If[y < 0, 2*d, d], 0],
      Dims[M] - If[dM > 0, If[y < 0, 2*dM, dM], 0]};
    InfinityQ[s] && AppendTo[out, vio[[1]]];
    OriginQ[s] && AppendTo[out, vio[[2]]];
    Do[AppendTo[out, If[MemberQ[ind, k], sig[M, k], "_"]]; If[printsep[M, k, Grade[s]],AppendTo[out,","],Nothing];,
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

V0 = MetricSignature[0]
\[DoubleStruckCapitalR] = MetricSignature[1]

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
  MetricSignature[n+Rank[b],option,BitOr[x,BitShiftLeft[BitAnd[y,Twiddle[DiffMask[b]]],Grade[b]]],Max[DiffVars[a],DiffVars[b]],Max[DiffMode[a],DiffMode[b]]]]

CirclePlus[Submanifold[v_,n_,x_,___],Submanifold[w_,m_,y_,___]] := Module[{b=IntegerQ[w],
    z = If[(DualQ[v]==DualQ[w])||(v!=w^T), Combine[v,w,x,y],BitOr[Mixed[v,x],Mixed[w,u]]]},
    Submanifold[If[IntegerQ[v], If[b, v+w, CirclePlus[MetricSignature[v],w]], If[b, CirclePlus[v,MetricSignature[W]], CirclePlus[v,w]]],CountOnes[Z],Z]]

Map[(MetricSignature /: Power[m:MetricSignature[_,#,___],i_Integer] := If[i==0,Return[V0],Nest[CirclePlus[m,#] &, m, i-1]]) &, Range[0,4]]
MetricSignature /: Power[MetricSignature[n_],i_Integer] := MetricSignature[n*i]
MetricSignature /: Power[MetricSignature[n_],i_Symbol] := MetricSignature[n*i]

(* conversions *)

Manifold[m_Submanifold] := m
Manifold[Submanifold[m_Integer, __]] := m
Manifold[Submanifold[m_Submanifold, __]] := m
(*MetricSignature[m:Submanifold[_,n_,_]] = MetricSignature[N,OptionsQ[m]](Vector(signbit.(V[:])),DiffVars[m],DiffMode[m])*)


