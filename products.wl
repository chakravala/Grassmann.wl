
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

derive[n_?NumberQ,b_] := 0
derive[n_,b_,a_,t_] := If[t,{a,derive[n,b]},{derive[n,b],a}]
derive[n_List,b_] := derive[n[[2]],b,n[[1]],True]

derivemul[V_,a_,b_,v_,x_?BooleanQ] := If[!(TangentSpaceQ[V] && DyadicQ[V]),v,Module[{sa,sb,ca,cb},
  {sa,sb} = {SymmetricSplit[V,a],SymmetricSplit[V,b]};
  {ca,cb} = {CountOnes[sa[[2]]],CountOnes[sb[[2]]]};
  If[(ca == cb == 0) || ((ca != 0) && (cb != 0)),v,Fold[derive,If[ca==0,If[x,1,v],If[x,v,1]], Map[GetBasis[v,#] &, IndexSplit[If[ca==0,sa,sb][[1]]]]]]
]]

derivemul[V_,a_,b_,x_,y_] := If[!(TangentSpaceQ[V] && DyadicQ[V]),x*y,Module[{sa,sb,ca,cb},
  {sa,sb} = {SymmetricSplit[V,a],SymmetricSplit[V,b]};
  {ca,cb} = {CountOnes[sa[[2]]],CountOnes[sb[[2]]]};
  If[(ca == cb == 0) || ((ca != 0) && (cb != 0)),x*y,
    prev = Fold[derive,If[ca==0,{a,b},{b,a}], Map[GetBasis[v,#] &, IndexSplit[If[ca==0,sa,sb][[1]]]]];
    While[SubmanifoldQ[prev[[1]]],
      prev = Fold[derive,{Coefficient[prev[[1]]],prev[[2]]}, Map[GetBasis[v,#] &, IndexSplit[Bits[prev[[1]]]]]]];
    If[ca==0,prev[[1]]*prev[[2]],prev[[2]]*prev[[1]]]
]]]

Map[Module[{c,p,h,ph,pn},
  {cc,pp} = {Symbol[StringJoin["Complement",ToString[#]]],Symbol[StringJoin["Parity",ToString[#]]]};
  {h,pg,pn} = {Symbol[StringJoin[ToString[cc],"Hodge"]],Symbol[StringJoin[ToString[pp],"Hodge"]],Symbol[StringJoin[ToString[pp],"Null"]]};
  Map[Module[{c = #[[1]], p = #[[2]], ch}, 
    ch = ToString[c]!=ToString[h];
    (*c[Chain[v_,g_,a_SparseArray]] := Module[{ib,val},
      {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      {d,q} = {DiffVars[v],If[ch,0,Boole[InfinityQ[v]]+Boole[OriginQ[v]]]};
      Chain[v,Dims[v]-g,SparseArray[Map[Rule[BitComplement[Dims[v],ib[[#]]-1,d,q]+1,Conjugate[p[v,ib[[#]]-1]*If[ch,pn[v,ib[[#]]-1,val[[#]]],val[[#]]]]] &,Range[Length[ib]]],Length[a]]]]*)
    c[Multivector[v_,a_SparseArray]] := Module[{ib,val},
      {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      {d,q} = {DiffVars[v],If[ch,0,Boole[InfinityQ[v]]+Boole[OriginQ[v]]]};
      Multivector[v,SparseArray[Map[Rule[BitComplement[Dims[v],ib[[#]]-1,d,q]+1,Conjugate[p[v,ib[[#]]-1]*If[ch,pn[v,ib[[#]]-1,val[[#]]],val[[#]]]]] &,Range[Length[ib]]],Length[a]]]]] &
,{{cc,pp},{h,pg}}]] &,{"Left","Right"}]

Map[Module[{p = Symbol[StringJoin["Parity",ToString[#]]]},
  (*Chain /: #[b:Chain[v_,g_,a_List]] := Module[{d=DiffVars[v]},
    If[d==0 && !p[g],b,
      out = SparseArray
      n = Dims[v];
      ib = IndexBasis[n,g];
      
      ]
  ];*)
  Chain /: #[b:Chain[v_,g_,a_SparseArray]] := If[DiffVars[v]==0,If[p[g],-b,b],
      Module[{ib,val},{ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      Chain[v,g,SparseArray[Map[Rule[ib[[#]],If[p[Grade[v,ib[[#]]-1]],-val[[#]],val[[#]]]] &,Range[Length[ib]]],Length[a]]]]];
  Multivector /: #[b:Multivector[v_,a_SparseArray]] := Module[{ib,val},
      {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      Multivector[v,SparseArray[Map[Rule[ib[[#]],If[p[Grade[v,ib[[#]]-1]],-val[[#]],val[[#]]]] &,Range[Length[ib]]],Length[a]]]]] &,
{Reverse,Conjugate}]

Map[Module[{p = Symbol[StringJoin["Parity",ToString[#]]]},
  #[b:Chain[v_,g_,a_SparseArray]] := If[DiffVars[v]==0,If[p[g],-b,b],
      Module[{ib,val},{ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      Chain[v,g,SparseArray[Map[Rule[ib[[#]],If[p[Grade[v,ib[[#]]-1]],-val[[#]],val[[#]]]] &,Range[Length[ib]]],Length[a]]]]];
  #[b:Multivector[v_,a_SparseArray]] := Module[{ib,val},
      {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      Multivector[v,SparseArray[Map[Rule[ib[[#]],If[p[Grade[v,ib[[#]]-1]],-val[[#]],val[[#]]]] &,Range[Length[ib]]],Length[a]]]]] &,
{Involute,Clifford}]


