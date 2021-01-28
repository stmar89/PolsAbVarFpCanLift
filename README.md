# PolsAbVarFpCanLift

Description
--

Magma Implementations for *Polarizations of abelian varieties over finite fields via canonical liftings*, by Jonas Bergström, Valentijn Karemaker and Stefano Marseglia.

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Details
--
This package requires [`stmar89/AbVarFq`](https://github.com/stmar89/AbVarFq).

The file `AlmOrd.m` contains the function `overorders_maximal_at_ss` that given as input an `IsogenyClassFq` of almost-ordinary squarefree abelian varieties in odd characteristic returns the over-orders of ZZ[F,V] which are maximal at the supersingular part of the endomorphism algebra. These and only these are endomorphism rings of abelian varieties in such an isogeny class.
See Oswal-Shankar (below) for more details.

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

Moreover there are the auxiliary intrinsics `RationalSplittingField`, `pAdicSplittingField`, EmbeddingOfSplittingFields` and `ComplexRoots`. For the description of those and more details in general can be found in the file itself.

In the file `examples.txt` there is the code for the examples in our paper. Such code is also intended as a guide on how to use the various functions and intrisics to compute isomorphism classes and principal polarizations.

Future Plans
--
Eventually this packages will become a submodule of [`stmar89/AbVarFq`](https://github.com/stmar89/AbVarFq) and the functionalities will be included in the correspoding intrinsic.

References
--

Ching-Li Chai, Brian Conrad, and Frans Oort,
*Complex multiplication and lifting problems*,
Mathematical Surveys and Monographs, vol. 195, American Mathematical Society, Providence, RI, 2014.

Abhishek Oswal and Ananth N. Shankar,
*Almost ordinary abelian varieties over finite fields*,
Journal of the London Mathematical Society 101 (2020), no. 3, 923–937.


