
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

mul[a:Submanifold[V_,_,ba_,___],b:Submanifold[V_,_,bb_,___]] := mul[a,b,derivemul[V,ba,bb,1,True]]
mul[a:Submanifold[V_,_,ba_,___],b:Submanifold[V_,_,bb_,___],der_] := If[DiffCheck[V,ba,bb] || der==0,Return[GZero[V]],Module[{A,B,Q,Z,pcc,bas,cc,d,out},
    {A,B,Q,Z} = SymmetricMask[V,ba,bb];
    {pcc,bas,cc} = If[InfQ[V] && OriginQ[V], Conformal[V,A,B], {False,BitXor[A,B],False}];
    d = GetBasis[V,BitOr[bas,Q]];
    out = If[MetricSignatureQ[V] || CountOnes[BitAnd[A,B]]==0,If[Xor[Parity[a,b],pcc],-d,d],Times[Times[If[pcc,-1,1],ParityInner[V,A,B]],d]];
    If[(DiffVars[V]!=0)&&(Z!=0),out = Times[GetBasis[LowOrder[V],Z],out],Nothing];
    If[cc, Module[{v=Coefficient[out]}, out+Times[GetBasis[V,BitXor[ConformalMask[V],BitOr[bas,Q]]],If[InfinityOriginQ[V,A,B],-v,v]]], out]
]]

Submanifold /: Times[a:Submanifold[V_,_,A_,x_],b:Submanifold[V_,_,B_,y_]] := Module[{v=derivemul[V,A,B,x,y]},Times[v,mul[a,b,v]]]
Submanifold /: NonCommutativeMultiply[a:Submanifold[V_,_,A_,x_],b:Submanifold[V_,_,B_,y_]] := Module[{v=derivemul[V,A,B,x,y]},Times[v,mul[a,b,v]]]
(*Submanifold /: Times[a:Submanifold[V_,__],b:Submanifold[V_,__]] := mul(a,b)*)

Tangiply[V_,Z_,v_] := If[SubmanifoldQ[v],Submanifold[v,GetBasis[LowOrder[V],Z]],Submanifold[v,GetBasis[V,Z]]];

Submanifold /: Wedge[a:Submanifold[V_,_,X_,x_],b:Submanifold[V_,_,Y_,y_]] := Module[{A,B,Q,Z,v},
  {A,B,Q,Z} = SymmetricMask[V,X,Y];
  If[CountOnes[BitAnd[A,B]]>0 || DiffCheck[V,X,Y],Return[GZero[V]],Nothing];
  v = derivemul[V,X,Y,x,y];
  If[TangentSpaceQ[V] && Z!=0,
    v = Tangiply[V,Z,v];
    If[CountOnes[Q]+Order[v]>DiffMode[V],Return[GZero[V]],Nothing]];
  Submanifold[If[Parity[a,b],-v,v],GetBasis[V,BitOr[BitXor[A,B],Q]]]]

Submanifold /: Vee[a:Submanifold[V_,_,X_,x_],b:Submanifold[V_,_,Y_,y_]] := Module[{p,c,t,Z,v},
  {p,c,t,Z} = Regressive[V,X,Y];
  If[!t,Return[GZero[V]],Nothing];
  v = derivemul[V,X,Y,x,y];
  If[TangentSpaceQ[V] && Z!=0,Module[{A,B,Q,z},
    {A,B,Q,z} = SymmetricMask[V,X,Y];
    v = Tangiply[V,Z,v];
    If[CountOnes[Q]+Order[v]>DiffMode[V],Return[GZero[V]],Nothing]]];
  Submanifold[If[OneQ[p],v,p*v],GetBasis[V,c]]]

Contraction[a:Submanifold[V_,_,X_,x_],b:Submanifold[V_,_,Y_,y_]] := Module[{g,c,t,Z,v},
  {g,c,t,Z} = Interior[V,X,Y];
  If[!t,Return[GZero[V]],Nothing];
  v = derivemul[V,X,Y,x,y]; (*use Dot product?*)
  If[TangentSpaceQ[V] && Z!=0,Module[{A,B,Q,z},
    {A,B,Q,z} = SymmetricMask[V,X,Y];
    v = Tangiply[V,Z,v];
    If[CountOnes[Q]+Order[v]>DiffMode[V],Return[GZero[V]],Nothing]]];
  Submanifold[If[MetricSignatureQ[V],If[g,-v,v],g*v],GetBasis[V,c]]]

Submanifold /: Dot[a_Submanifold,b_Submanifold] := Contraction[a,b]

Submanifold /: Cross[a_Submanifold,b_Submanifold] := HodgeDual[Wedge[a,b]]

(* products *)

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

(* unary *)

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

