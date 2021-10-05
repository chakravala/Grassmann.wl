
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
