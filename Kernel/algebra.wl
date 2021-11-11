
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

distprod[name_,v_,a_,b_] := NormalMerge@Map[name[v,#[[1]],#[[2]]]&,Distribute[{a,b},List]]

product[name_,a:Multivector[v_,A_],b:Multivector[v_,B_]] :=
  Multivector[v,distprod[name,v,Drop[ArrayRules@A, -1],Drop[ArrayRules@B, -1]]]
product[name_,a:Submanifold[v_,_,A_,x_],b:Multivector[v_,B_]] :=
  Multivector[v,NormalMerge@Map[name[v,A->x,#] &, Drop[ArrayRules@B,-1]]]
product[name_,a:Multivector[v_,A_],b:Submanifold[v_,_,B_,y_]] :=
  Multivector[v,NormalMerge@Map[name[v,#,B->y] &, Drop[ArrayRules@A,-1]]]
product[name_,Submanifold[V_,_,X_,x_],Submanifold[V_,_,Y_,y_]] :=
  GetBasis[V,name[V,X,Y,x,y]]
product[name_,a:Chain[v_,_,_],b:Multivector[v_,B_]] :=
  Multivector[v,distprod[name,v,ChainToMulti@a,Drop[ArrayRules@B, -1]]]
product[name_,a:Multivector[v_,A_],b:Chain[v_,_,_]] :=
  Multivector[v,distprod[name,v,Drop[ArrayRules@A, -1],ChainToMulti@b]]

product[name_,a:Chain[v_,A_,_],b:Chain[v_,B_,_],g_] :=
  Chain[v,g,distprod[name,v,ChainToMulti@a,ChainToMulti@b]]
product[name_,a:Submanifold[v_,_,A_,x_],b:Chain[v_,B_,_],g_] :=
  Chain[v,g,distprod[name,v,{A->x},ChainToMulti@b]]
product[name_,a:Chain[v_,A_,_],b:Submanifold[v_,_,B_,y_],g_] :=
  Chain[v,g,distprod[name,v,ChainToMulti[a],{B->y}]]

product[GeomMulti,a:Chain[v_,0,A_],b:Chain[v_,g_,B_]] := Chain[v,g,A[[1]]*B]
product[GeomMulti,a:Chain[v_,g_,A_],b:Chain[v_,0,B_]] := Chain[v,g,A*B[[1]]]
product[GeomMulti,a:Submanifold[v_,0,_,A_],b:Chain[v_,g_,B_]] := Chain[v,g,A*B]
product[GeomMulti,a:Chain[v_,g_,A_],b:Submanifold[v_,0,_,B_]] := Chain[v,g,A*B]

product[GeomMulti,a:Chain[v_,l_,A_],b:Chain[v_,g_,B_]] :=
  If[g==Dims[v] && !TangentSpaceQ[v], ComplementRightHodge[Reverse[a]]*Chain[v,0,B],
  If[l==Dims[v] && !TangentSpaceQ[v], Chain[v,0,A]*ComplementLeftHodge[Reverse[b]],
  Multivector[v,distprod[GeomMulti,v,ChainToMulti@a,ChainToMulti@b]]]]
product[GeomMulti,a:Submanifold[v_,l_,x_,A_],b:Chain[v_,g_,B_]] :=
  If[g==Dims[v] && !TangentSpaceQ[v], ComplementRightHodge[Reverse[a]]*Chain[v,0,B],
  If[l==Dims[v] && !TangentSpaceQ[v], Submanifold[v,0,0,A]*ComplementLeftHodge[Reverse[b]],
  Multivector[v,distprod[GeomMulti,v,{x->A},ChainToMulti@b]]]]
product[GeomMulti,a:Chain[v_,l_,A_],b:Submanifold[v_,g_,y_,B_]] :=
  If[g==Dims[v] && !TangentSpaceQ[v], ComplementRightHodge[Reverse[a]]*Submanifold[v,0,0,B],
  If[l==Dims[v] && !TangentSpaceQ[v], Chain[v,0,A]*ComplementLeftHodge[Reverse[b]],
  Multivector[v,distprod[GeomMulti,v,ChainToMulti@a,{y->B}]]]]

product[JoinMulti,a:Chain[_,A_,_],b:Chain[_,B_,_]] := product[JoinMulti,a,b,A+B]
product[MeetMulti,a:Chain[v_,A_,_],b:Chain[v_,B_,_]] := product[JoinMulti,a,b,A+B-Dims[v]]
product[SkewMulti,a:Chain[v_,A_,_],b:Chain[v_,B_,_]] := If[A<B,GZero[v],product[JoinMulti,a,b,A-B]]
product[JoinMulti,a:Submanifold[_,A_,_,_],b:Chain[_,B_,_]] := product[JoinMulti,a,b,A+B]
product[MeetMulti,a:Submanifold[v_,A_,_,_],b:Chain[v_,B_,_]] := product[JoinMulti,a,b,A+B-Dims[v]]
product[SkewMulti,a:Submanifold[v_,A_,_,_],b:Chain[v_,B_,_]] := If[A<B,GZero[v],product[JoinMulti,a,b,A-B]]
product[JoinMulti,a:Chain[_,A_,_],b:Submanifold[_,B_,_]] := product[JoinMulti,a,b,A+B]
product[MeetMulti,a:Chain[v_,A_,_],b:Submanifold[v_,B_,_,_]] := product[JoinMulti,a,b,A+B-Dims[v]]
product[SkewMulti,a:Chain[v_,A_,_],b:Submanifold[v_,B_,_,_]] := If[A<B,GZero[v],product[JoinMulti,a,b,A-B]]

Map[Module[{prod=#[[1]],name=#[[2]]},
  name[v_,a_,b_,x_,y_] := name[v,a,b,derivemul[v,a,b,x,y]];
  name[v_,Rule[a_,x_],Rule[b_,y_]] := name[v,a,b,x,y];
  name[v_,Rule[a_,x_],Rule[List[b_],y_]] := name[v,a,b-1,x,y];
  name[v_,Rule[List[a_],x_],Rule[b_,y_]] := name[v,a-1,b,x,y];
  name[v_,Rule[List[a_],x_],Rule[List[b_],y_]] := name[v,a-1,b-1,x,y];
  Multivector /: prod[a_Multivector,b_Multivector] := product[name,a,b];
  Multivector /: prod[a_Submanifold,b_Multivector] := product[name,a,b];
  Multivector /: prod[a_Multivector,b_Submanifold] := product[name,a,b];
  Submanifold /: prod[a_Submanifold,b_Submanifold] := product[name,a,b];
  Chain /: prod[a_Chain,b_Submanifold] := product[name,a,b];
  Chain /: prod[a_Submanifold,b_Chain] := product[name,a,b];
  Chain /: prod[a_Chain,b_Multivector] := product[name,a,b];
  Chain /: prod[a_Multivector,b_Chain] := product[name,a,b];
  Chain /: prod[a_Chain,b_Chain] := product[name,a,b]] &,
{{Wedge,JoinMulti},{NonCommutativeMultiply,GeomMulti},{Times,GeomMulti},{Vee,MeetMulti},{Dot,SkewMulti}}]

Multivector /: Cross[a_Multivector,b_Multivector] := HodgeDual[Wedge[a,b]]
Multivector /: Cross[a_Submanifold,b_Multivector] := HodgeDual[Wedge[a,b]]
Multivector /: Cross[a_Multivector,b_Submanifold] := HodgeDual[Wedge[a,b]]
Submanifold /: Cross[a_Submanifold,b_Submanifold] := HodgeDual[Wedge[a,b]]
Chain /: Cross[a_Submanifold,b_Chain] := HodgeDual[Wedge[a,b]]
Chain /: Cross[a_Chain,b_Submanifold] := HodgeDual[Wedge[a,b]]
Chain /: Cross[a_Multivector,b_Chain] := HodgeDual[Wedge[a,b]]
Chain /: Cross[a_Chain,b_Multivector] := HodgeDual[Wedge[a,b]]
Chain /: Cross[a_Chain,b_Chain] := HodgeDual[Wedge[a,b]]

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

Map[Module[{c,p,h,ph,pn},
  {s,pp} = {SymbolJoin["Complement",#],SymbolJoin["Parity",#]};
  {h,pg,pn} = {SymbolJoin[s,"Hodge"],SymbolJoin[pp,"Hodge"],SymbolJoin[pp,"Null"]};
  Map[Module[{c = #[[1]], p = #[[2]], ch},
    ch = ToString[c]!=ToString[h];
    c[b:Submanifold[V_,G_,B_,x_]] := If[ZeroQ[x],GZero[V],Module[{e = ToString[c]!=ToString[h],z,v},
      z = If[e,0,Boole@InfinityQ@V+Boole@OriginQ@V];
      If[DyadicQ@V,Throw[domain],
        v = Conjugate[x]*If[e,pn[V,B,1],1];
        GetBasis[V,BitComplement[Dims@V,B,DiffVars@V,z],p[b]*v]]]];
    c[b:Chain[v_,g_,a_]] := Module[{d,q},
      {d,q} = {DiffVars@v,If[ch,0,Boole@InfinityQ@v+Boole@OriginQ@v]};
      Chain[v,Dims[v]-g,Map[Rule[BitComplement[Dims@v,#[[1]],d,q]+1,Conjugate[p[v,#[[1]]]*If[ch,pn[v,#[[1]],#[[2]]],#[[2]]]]] &,ChainToMulti@b]]];
    c[Multivector[v_,a_SparseArray]] := Module[{ib,val,d,q},
      {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
      {d,q} = {DiffVars@v,If[ch,0,Boole@InfinityQ@v+Boole@OriginQ@v]};
      Multivector[v,Map[Rule[BitComplement[Dims@v,ib[[#]]-1,d,q]+1,Conjugate[p[v,ib[[#]]-1]*If[ch,pn[v,ib[[#]]-1,val[[#]]],val[[#]]]]] &,Range[Length[ib]]]]]] &
,{{s,pp},{h,pg}}]] &,{"Left","Right"}]

Map[Module[{p = SymbolJoin["Parity",#]},
  Submanifold /: #[b:Submanifold[v_,_,B_,_]] := If[Coefficient[b]!=0,If[p[Grade[v,B]],Minus@b,b],GZero@v];
  Chain /: #[b:Chain[v_,g_,a_]] := If[DiffVars[v]==0,If[p[g],Minus@b,b],
    Chain[v,g,Map[Rule[#[[1]]+1,If[p@Grade[v,#[[1]]],-#[[2]],#[[2]]]] &,ChainToMulti@b]]];
  Multivector /: #[b:Multivector[v_,a_SparseArray]] := Module[{ib,val},
    {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
    Multivector[v,Map[Rule[ib[[#]],If[p@Grade[v,ib[[#]]-1],-val[[#]],val[[#]]]] &,Range[Length[ib]]]]]] &,
{Reverse,Conjugate}]

Map[Module[{p = Symbol[StringJoin["Parity",ToString[#]]]},
  #[b:Submanifold[v_,_,B_,_]] := If[Coefficient[b]!=0,If[p[Grade[v,B]],Minus@b,b],GZero@v];
  #[b:Chain[v_,g_,a_]] := If[DiffVars[v]==0,If[p[g],Minus@b,b],
    Chain[v,g,Map[Rule[#[[1]]+1,If[p@Grade[v,#[[1]]],-#[[2]],#[[2]]]] &,ChainToMulti@a]]];
  #[b:Multivector[v_,a_SparseArray]] := Module[{ib,val},
    {ib,val} = {a["AdjacencyLists"],a["NonzeroValues"]};
    Multivector[v,Map[Rule[ib[[#]],If[p@Grade[v,ib[[#]]-1],-val[[#]],val[[#]]]] &,Range[Length[ib]]]]]] &,
{Involute,Clifford}]

(* algebra *)

Submanifold[m_, g_, b_] := Submanifold[m, g, b, 1]
Submanifold[x_,s:Submanifold[v_,g_,b_,y_]] := Submanifold[v,g,b,Times[x,y]]

Submanifold /: Plus[Submanifold[m_, g_, a_, x_],Submanifold[m_, g_, b_, y_]] :=
  Chain[m,g,{a+1->x,b+1->y}]
Submanifold /: Plus[Submanifold[m_, _, a_, x_],Submanifold[m_, _, b_, y_]] :=
  Multivector[m,{a+1->x,b+1->y}]
Chain /: Plus[a:Chain[v_,g_,_],b:Submanifold[v_,g_,B_,y_]] :=
  Chain[v,g,NormalMerge@Join[RuleShift/@ChainToMulti@a,{B+1->y}]]

Submanifold /: Minus[Submanifold[v_,g_,b_,x_]] := Submanifold[v,g,b,Minus@x]
Submanifold /: Minus[a_Submanifold,b_Submanifold] := Plus[a,Minus@b]
Multivector /: Minus[Multivector[m_, a_]] := Multivector[m, Minus@a]
Multivector /: Minus[a_Multivector,b_Submanifold] := Plus[a,Minus@b]
Multivector /: Minus[a_Multivector,b_Chain] := Plus[a,Minus@b]
Chain /: Minus[Chain[m_, g_, a_]] := Chain[m, g, Minus@a]
Chain /: Minus[a_Chain,b_Submanifold] := Plus[a,Minus@b]
Chain /: Minus[a_Submanifold,b_Chain] := Plus[a,Minus@b]
Chain /: Minus[a_Chain,b_Submanifold] := Plus[a,Minus@b]

Map[Module[{},
  Chain /: #[Chain[m_, g_, x_], Chain[m_, g_, y_]] := Chain[m, g, #[x,y]];
  Multivector /: #[Multivector[m_, x_], Multivector[m_, y_]] := Multivector[m, #[x,y]];
  Submanifold /: #[Submanifold[m_, g_, b_, x_],Submanifold[m_, g_, b_, y_]] := Submanifold[m,g,b,#[x,y]];
  Multivector /: #[a_Submanifold,b_Multivector] := #[Multivector[a],b];
  Multivector /: #[a_Chain,b_Multivector] := #[Multivector[a],b];
  Chain /: #[a_Submanifold,b_Chain] := #[Multivector[a],b]] &,
{Plus,Minus}]

Submanifold /: Total[t:Submanifold[m_, g_, b_, _]..] := Submanifold[m,g,b,Total[Coefficient/@t]]
Submanifold /: Total[t:Submanifold[m_, g_ ,_, _]..] := Chain[m,g,NormalMerge@Map[Rule[#,Dims[m]] &, {t}]]
Submanifold /: Total[t:Submanifold[m_, _, _, _]..] := Multivector[m,NormalMerge@Rule/@{t}]
Chain /: Total[t:Chain[m_,g_,_]..] := Chain[m,g,Total[Map[Coefficient,{t}]]]
Multivector /: Total[t:Multivector[m_,_]..] := Multivector[m,Total[Map[Coefficient,{t}]]]

(*UpValues[Submanifold] = Join[UpValues[Submanifold],{
	HoldPattern[Total[t:Submanifold[m_, g_, b_, _]..] :> Times[{t}[[1]],Total[Map[Coefficient,{t}]]]],
	HoldPattern[Total[t:Submanifold[m_, g_ ,_, _]..] :> Module[{n=Dims[m]},Chain[m,g,SparseArray[Normal@Merge[Map[Rule[#,n] &, {t}],Total],Binomial[n,g]]]]],
	HoldPattern[Total[t:Submanifold[m_, _, _, _]..] :> Multivector[m,SparseArray[Normal@Merge[Map[Rule, {t}],Total],BitShiftLeft[1,Dims[m]],Total]]]}];
UpValues[Submanifold] = SubsetMap[Reverse, UpValues[Submanifold], -3 ;; -1];*)
