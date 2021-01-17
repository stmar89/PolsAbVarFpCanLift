# PolsAbVarFpCanLift

Description
--

Magma Implementations for *Polarizations of abelian varieties over finite fields via canonical liftings*, by Jonas Bergström, Valentijn Karemaker and Stefano Marseglia.

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Details
--
This package requires [`stmar89/AbVarFq`](https://github.com/stmar89/AbVarFq).

The file `AlmOrd.m` contains the function `overorders_maximal_at_ss` that given as input an `IsogenyClassFq` of almost-ordinary squarefree abelian varieties in odd characteristic returns the over-orders of ZZ[F,V] which are maximal at the supersingular part of the endomorphism algebra. These and only these are endomorphism rings of abelian varieties in such an isogeny class.

The file `ResRefCond.m` contains the intrinsic `ResidualReflexCondition` which take as input an `IsogenyClassFq` and returns a sequence of `AlgAssCMType` which satisfy the Residual Reflex Condition (RRC).

More details can be found in the files.

In the file `examples.txt` there is the code for the examples in our paper. Such code is also intended as a guide on how to use the various functions to compute isomorphism classes and principal polarizations.

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


