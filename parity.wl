
(* This file is part of Grassmann. It is licensed under the AGPL license *)
(* Grassmann Copyright (C) 2021 Michael Reed *)

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
    {If[t, If[Xor[p,ParityRight[0,Total[Indices[B]],CountOnes[B]]], -1, 1], 1], BitOr[c,Q], t, Z}]]]

ParityInterior[v_,a_,b_] := Module[{A,B,Q,Z,n},
  {A,B,Q,Z} = SymmetricMask[v,a,b]; n = Rank[v];
  If[DiffCheck[v,A,B] || cga[v,A,B],{False,0,False,Z},Module[{p,c,t,z,ind,g},
    {p,c,t,z} = ParityRegressive[MetricSignature[v],A,BitComplement[n,B,DiffVars[v]],True];
    ind = Indices[B]; g = MetricProduct[v,ind];
    {If[t, If[Xor[p,ParityRight[0,Total[ind],CountOnes[B]]], -g, g], g], BitOr[c,Q], t, Z}]]]

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

Map[Module[{calc = Symbol[StringJoin[{"Parity",ToString[#]}]]},
  #[v_,a_,b_] := If[Dims[Supermanifold[v]] > SparseLimit,
    calc[v,a,b],#[v,a,b] = calc[v,a,b]];
  (*#[Submanifold[v_,_,b_,_],Submanifold[v_,_,c_,_]] := #[v,a,b];*)
] &, {Conformal,Regressive,Interior}]


