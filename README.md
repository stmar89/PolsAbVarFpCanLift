# PolsAbVarFpCanLift

Description
--

Magma Implementations for *Polarizations of abelian varieties over finite fields via canonical liftings*, by Jonas Bergström, Valentijn Karemaker and Stefano Marseglia.

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Details
--
This package requires [`stmar89/AbVarFq`](https://github.com/stmar89/AbVarFq) and its dependencies.

The file `ResRefCond.m` contains code to check wheter a CM-type satisfies the Shimura-Taniyama formula and the Residual Reflex Condition (RRC). Recall that a CMType PHI satisfies RRC if: 
    *) the CM-type satisfies the Shimura-Taniyama formula, and
    *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
See Chai-Conrad-Oort (below) for more details about RRC.

The main intrinsics are:
- `ShimuraTaniyama(AVh,PHI)` : returns wheter a CM-type PHI satisfies the Shimura-Taniyama formula for the Forbenius of the Isogeny class AVh.
- `pAdicReflexField(AVh,PHI)` : given an isogeny class AVh and a CM-type PHI returns the reflex field associated to PHI as a p-adic field.
- `IsResidueReflexFieldEmbeddable(AVh,PHI)` : given an isogeny class AVh over FFq returns the if the residue field of reflex field associated to the CM-type can be embedded in FFq.
- `ResidualReflexCondition(AVh,PHI)` : given an isogeny class AVh and a CM-type PHI returns whether PHI satisfies the residual reflex conditon (RRC). 
- `ResidualReflexCondition(AVh)` : given an isogeny class AVh returns the sequence of CM-types that satisfy RRC.

The package provides several auxiliary intrinsics, including `RationalSplittingField`, `pAdicSplittingField`, `EmbeddingOfSplittingFields` and `ComplexRoots`, that allow to perform intermediate computations. Severeal computations can be performed using different methods. 

For complete complete descriptions and more details we refer to the [`List of functions`](https://github.com/stmar89/PolsAbVarFpCanLift/blob/main/List_of_functions.md).

In the file [`examples.txt`](https://github.com/stmar89/PolsAbVarFpCanLift/blob/main/examples.txt) there is the code for the examples in our paper. Such code is also intended as a guide on how to use the various functions and intrisics to compute isomorphism classes and principal polarizations.

The file [`additional_examples.pdf`](https://github.com/stmar89/PolsAbVarFpCanLift/blob/main/additional_examples.pdf) contains cumulative tables of computations for squarefree isogeny classes over small finite fields of small dimension.

Legacy (kept for retrocompatibility)
--
The content of the file `AlmOrd.m` has been superseeded by the new code contained in [`IsomClAbVarFqCommEndAlg`](https://github.com/stmar89/IsomClAbVarFqCommEndAlg). 
The file `AlmOrd.m` contains the function `overorders_maximal_at_ss` that given as input an `IsogenyClassFq` of almost-ordinary squarefree abelian varieties in odd characteristic returns the over-orders of ZZ[F,V] which are maximal at the supersingular part of the endomorphism algebra. These and only these are endomorphism rings of abelian varieties in such an isogeny class. 
See Oswal-Shankar (below) for more details.

References
--

Ching-Li Chai, Brian Conrad, and Frans Oort,
*Complex multiplication and lifting problems*,
Mathematical Surveys and Monographs, vol. 195, American Mathematical Society, Providence, RI, 2014.

Abhishek Oswal and Ananth N. Shankar,
*Almost ordinary abelian varieties over finite fields*,
Journal of the London Mathematical Society 101 (2020), no. 3, 923–937.


