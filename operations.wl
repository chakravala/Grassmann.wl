
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

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

Map[(MetricSignature /: Power[m:MetricSignature[_,#,___],i_Integer] := If[i==0,Return[V0],Nest[CirclePlus[m,#] &, m, i-1]]) &, Range[0,4]]
MetricSignature /: Power[MetricSignature[n_],i_Integer] := MetricSignature[n*i]

(* conversions *)

Manifold[m_Submanifold] := m
Manifold[Submanifold[m_Integer, __]] := m
Manifold[Submanifold[m_Submanifold, __]] := m
(*MetricSignature[m:Submanifold[_,n_,_]] = MetricSignature[N,OptionsQ[m]](Vector(signbit.(V[:])),DiffVars[m],DiffMode[m])*)

(* operations *)

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
  (*pg[m_Integer,bits_Integer] := pg[m,bits,CountOnes[bits]];
  pg[m_Integer,bits_Integer,grade_] := If[Xor[p[0,Total[Indices[BitAnd[bits,BitShiftLeft[1,Dims[m]-DiffVars[m]]]-1]],grade,Dims[m]-DiffVars[m]],ConformalQ[m] && (BitAnd[bits,3]==2)],-1,1];*)
  p[V_Submanifold,B_] := p[V,B,CountOnes[B]];
  pg[V_Submanifold,B_] := pg[V,B,CountOnes[B]];
  p[V_Submanifold,B_,G_] := If[p[0,Total[Indices[BitAnd[B,BitShiftLeft[1,Dims[V]-DiffVars[V]]-1]]],G,Dims[V]-DiffVars[v]],-1,1];
  pg[V_Submanifold,B_,G_] := Module[{dd = Dims[V]-DiffVars[V], ind, g},
    ind = Indices[BitAnd[B,BitShiftLeft[1,dd]-1]];
    g = MetricProduct[V,ind];
    If[Xor[p[0,Total[ind],G,dd],ConformalQ[V] && (BitAnd[B,3] == 2)],-g,g]];
  p[Submanifold[V_,G_,B_,___]] := p[V,B,G];
  pg[Submanifold[V_,G_,B_,___]] := pg[V,B,G]] &,
{"Left","Right"}]
 
BitComplement[dim_Integer,bits_Integer,d_Integer:0,p_Integer:0] := Module[{up,nd,c},
    {up,nd} = {BitShiftLeft[1,If[p==1,0,p]-1], dim-d};
    c = BitOr[BitAnd[Twiddle[bits],BitXor[up,BitShiftLeft[1,nd]-1]],BitAnd[bits,BitXor[up,BitShiftLeft[BitShiftLeft[1,d]-1,nd]]]];
    If[CountOnes[BitAnd[c,up]]≠1, BitXor[c,up], c]]



Map[Module[{s = Symbol[StringJoin["Complement",#]], p = Symbol[StringJoin["Parity",#]], h, pg, pn},
  {h,pg,pn} = {Symbol[StringJoin[ToString[s],"Hodge"]],Symbol[StringJoin[ToString[p],"Hodge"]],Symbol[StringJoin[ToString[p],"Null"]]};
  Map[Module[{c = #[[1]], p = #[[2]]},
    c[b:Submanifold[V_,G_,B_,x_]] := If[x==0,GZero[V],Module[{e = ToString[c]!=ToString[h],d,z,v},
      z = If[e,0,InfinityQ[V]+OriginQ[V]];
      d = GetBasis[V,BitComplement[Dims[V],B,DiffVars[V],z]];
      If[DyadicQ[V],Throw[domain],
        v = Conjugate[x]*If[e,pn[V,B,Coefficient[d]],Coefficient[d]];
        If[MetricSignatureQ[V],If[p[b],Submanifold[-v,d],If[OneQ[v],d,Submanifold[v,d]]],Submanifold[p[b]*v,d]]]]]] &
  ,{{s,p},{h,pg}}]] &,{"Left","Right"}]
 
