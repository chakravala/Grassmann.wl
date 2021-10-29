
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

Tangiply[V_,Z_,v_] := If[SubmanifoldQ[v],Submanifold[v,GetBasis[LowOrder[V],Z]],Submanifold[v,GetBasis[V,Z]]];

JoinMulti[v_,a_Integer,b_Integer,x_] := Module[{A,B,Q,Z,val},
  If[ZeroQ[x] || DiffCheck[v,a,b],Nothing,
    {A,B,Q,Z} = SymmetricMask[v,a,b];
    If[CountOnes[BitAnd[A,B]]>0,Nothing,
    val = Times[ParityInner[v,a,b],x];
    If[TangentSpaceQ[v],If[Z!=0,val*=GetBasis[LowOrder[v],Z],Nothing];
      If[CountOnes[Q]+Order[val]>DiffMode[v],Return[Nothing],Nothing],Nothing];
    Rule[BitOr[BitXor[A,B],Q]+1,val]]]]

GeomMulti[v_,a_Integer,b_Integer,x_] := Module[{A,B,Q,Z,pcc,bas,cc,val},
  If[ZeroQ[x] || DiffCheck[v,a,b],Nothing,
    {A,B,Q,Z} = SymmetricMask[v,a,b];
    {pcc,bas,cc} = If[InfinityQ[v]&&OriginQ[v],Conformal[v,A,B],{False,BitXor[A,B],False}];
    val = Times[ParityInner[v,a,b],If[pcc,-x,x]];
    If[TangentSpaceQ[v],If[Z!=0,val*=GetBasis[LowOrder[v],Z],Nothing];
      If[CountOnes[Q]+Order[val]>DiffMode[v],Return[Nothing],Nothing],Nothing];
    If[cc,Sequence[Rule[BitOr[bas,Q],val],Rule[BitOr[BitXor[ConformalMask[v],bas],Q]+1,If[InfinityOriginQ[v,A,B],-val,val]]],Rule[BitOr[bas,Q]+1,val]]]]

MeetMulti[v_,a_Integer,b_Integer,x_] := Module[{g,c,t,z,val},
  If[ZeroQ[x],Nothing,
    {g,c,t,z} = Regressive[v,a,b];
    val = x;
    If[TangentSpaceQ[v],If[Z!=0,Module[{aa,bb,Q,cc},
      {aa,bb,Q,cc} = SymmetricMask[v,a,b];
      val*=GetBasis[LowOrder[v],Z];
      If[CountOnes[Q]+Order[val]>DiffMode[v],Return[Nothing],Nothing]],Nothing],Nothing];
    If[t,Rule[c+1,Times[g,val]],Nothing]]]

SkewMulti[v_,a_Integer,b_Integer,x_] := Module[{g,c,t,z,val},
  If[ZeroQ[x],Nothing,
    {g,c,t,z} = Interior[v,a,b];
    val = x;
    If[TangentSpaceQ[v],If[Z!=0,Module[{aa,bb,Q,cc},
      {aa,bb,Q,cc} = SymmetricMask[v,a,b];
      val*=GetBasis[LowOrder[v],Z];
      If[CountOnes[Q]+Order[val]>DiffMode[v],Return[Nothing],Nothing]],Nothing],Nothing];
    If[t,Rule[c+1,Times[g,val]],Nothing]]]

product[name_,a:Multivector[v_,A_],b:Multivector[v_,B_]] :=
  Multivector[v,SparseArray[Map[name[v,#[[1]],#[[2]]] &,
    Distribute[{Drop[ArrayRules[A], -1],Drop[ArrayRules[B], -1]}, List]], Length[A]]]
product[name_,a:Submanifold[v_,_,A_,x_],b:Multivector[v_,B_]] :=
  Multivector[v,SparseArray[Map[name[v,{A+1}->x,#] &, Drop[ArrayRules[B],-1]], Length[B]]]
product[name_,a:Multivector[v_,A_],b:Submanifold[v_,_,B_,y_]] :=
  Multivector[v,SparseArray[Map[name[v,#,{B+1}->y] &, Drop[ArrayRules[A],-1]], Length[A]]]
product[name_,Submanifold[V_,_,X_,x_],Submanifold[V_,_,Y_,y_]] :=
  GetBasis[V,name[V,X,Y,x,y]]

Map[Module[{prod=#[[1]],name=#[[2]]},
  name[v_,a_,b_,x_,y_] := name[v,a,b,derivemul[v,a,b,x,y]];
  name[v_,Rule[List[a_],x_],Rule[List[b_],y_]] := name[v,a-1,b-1,x,y];
  Multivector /: prod[a_Multivector,b_Multivector] := product[name,a,b];
  Multivector /: prod[a_Submanifold,b_Multivector] := product[name,a,b];
  Multivector /: prod[a_Multivector,b_Submanifold] := product[name,a,b];
  Submanifold /: prod[a_Submanifold,b_Submanifold] := product[name,a,b]] &,
{{Wedge,JoinMulti},{NonCommutativeMultiply,GeomMulti},{Times,GeomMulti},{Vee,MeetMulti},{Dot,SkewMulti}}]
(*{{Wedge,JoinChain},{NonCommutativeMultiply,GeomChain},{Times,GeomChain},{Vee,MeetChain},{Dot,SkewChain}}*)

Multivector /: Cross[a_Multivector,b_Multivector] := HodgeDual[Wedge[a,b]]
Multivector /: Cross[a_Submanifold,b_Multivector] := HodgeDual[Wedge[a,b]]
Multivector /: Cross[a_Multivector,b_Submanifold] := HodgeDual[Wedge[a,b]]
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
  If[(ca == cb == 0) || ((ca != 0) && (cb != 0)),x*y,Module[{prev},
    prev = Fold[derive,If[ca==0,{a,b},{b,a}], Map[GetBasis[v,#] &, IndexSplit[If[ca==0,sa,sb][[1]]]]];
    While[SubmanifoldQ[prev[[1]]],
      prev = Fold[derive,{Coefficient[prev[[1]]],prev[[2]]}, Map[GetBasis[v,#] &, IndexSplit[Bits[prev[[1]]]]]]];
    If[ca==0,prev[[1]]*prev[[2]],prev[[2]]*prev[[1]]]
]]]]

(* unary *)

Multivector /: Transpose[Multivector[v_,a_SparseArray]] := If[DyadicQ[v],Module[{ib,val},
  {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
  Multivector[v,SparseArray[Map[Rule[Dual[v,ib[[#]]-1,Dims[v]/2]+1,Conjugate[val[[#]]]]] &,Range[Length[ib]],Length[a]]]],Multivector[Dual[v],Map[Conj,a]]]

Unprotect[\[FivePointedStar]]
\[FivePointedStar] = HodgeDual
Protect[\[FivePointedStar]]
Submanifold /: HodgeDual[s_Submanifold] := ComplementRightHodge[s]
Multivector /: HodgeDual[s_Multivector] := ComplementRightHodge[s]
Chain /: HodgeDual[s_Chain] := ComplementRightHodge[s]

Map[Module[{s = Symbol[StringJoin["Complement",#]], p = Symbol[StringJoin["Parity",#]], h, pg, pn},
  {h,pg,pn} = {Symbol[StringJoin[ToString[s],"Hodge"]],Symbol[StringJoin[ToString[p],"Hodge"]],Symbol[StringJoin[ToString[p],"Null"]]};
  Map[Module[{c = #[[1]], p = #[[2]]},
    c[b:Submanifold[V_,G_,B_,x_]] := If[ZeroQ[x],GZero[V],Module[{e = ToString[c]!=ToString[h],z,v},
      z = If[e,0,Boole[InfinityQ[V]]+Boole[OriginQ[V]]];
      If[DyadicQ[V],Throw[domain],
        v = Conjugate[x]*If[e,pn[V,B,1],1];
        GetBasis[V,BitComplement[Dims[V],B,DiffVars[V],z],p[b]*v]]]]] &
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
    c[Multivector[v_,a_SparseArray]] := Module[{ib,val,d,q},
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

