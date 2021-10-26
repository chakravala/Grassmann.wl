<p align="center">
  <img src="./Assets/Images/logo.png" alt="Grassmann.wl"/>
</p>

# Grassmann.wl

*⟨Leibniz-Grassmann-Clifford-Hestenes⟩ differential geometric algebra / multivector simplicial complex*

This repository is an official Wolfram language variation of the [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) library originally implemented in the Julia language.
Currently, this is a casual work in progress.

To make this paclet visible to the system, install this repository to an Applications folder:
```wolfram
PacletDirectoryLoad[FileNameJoin[{$UserBaseDirectory, "Applications", "Grassmann.wl"}]]
```
Code from package can be loaded with ``Needs["Grassmann`"]`` or ``Get["Grassmann`"]`` to initialize.

## Preview

Preliminary usage information can be found in the WSS21 post [Foundations of differential geometric algebra package](https://community.wolfram.com/groups/-/m/t/2314523) before the documentation is created. This post is currently outdated, as the exterior product and geometric product are now implemented in this repository. Updated documentation will be created soon, as finishing touches are ironed out.

In Grassmann, a standard vector space is initialized with `Submanifold[dimension]`, the definition of which will be explained further later. The Grassmann package is intended for universal interoperability of the abstract tensor algebra type system. All tensor algebra subtypes have type parameter `V`, used to store a tensor bundle value. This means that different packages can create tensor types having a common underlying tensor bundle structure. For example, this is mainly used in Grassmann to define various sub algebra, tensor basis and mixed tensor types. The key to making the interoperability work is that each tensor algebra type shares a tensor bundle parameter, which contains all the info needed to make decisions about algebra. So other packages need only use the vector space information to generate the implementation of an a desired algebra.

The elements of the algebra can be generated in many ways using the Submanifold elements:
```wolfram
V = Submanifold[3]
v = Submanifold[V,0]
Wedge[v[3],v[1,2] + v[1,3]]
GeometricAlgebraBasis[V]
```
Some common operations include `Wedge, Vee, Dot, NonCommutativeMultiply, ComplementRightHodge`.

Once finishing touches are ironed out, more documentation will be created.
