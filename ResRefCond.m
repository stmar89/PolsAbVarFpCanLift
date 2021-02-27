/* vim: set syntax=magma : */
/*
    Magma implementation for
        "Polarizations of abelian varieties over finite fields via canonical liftings", 
         by Jonas Bergström, Valentijn Karemaker and Stefano Marseglia.

    Please send bug reports and comments to 
        Stefano Marseglia, stefano.marseglia89@gmail.com


    Code to compute the CM-types that satisfy the Residual Reflex Condition (RRC),
    introduced by Chai-Conrad-Oort in 'Complex Multiplication and Lifting Problems'

    Recall that a CMType PHI satisfies RRC if: 
        *) the CM-type satisfies the Shimura-Taniyama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.

*/


declare verbose ResRefCond, 2;

// TODO : 
//   - some precision issues which seem to be triggered by Magma. Reports have been sent in Fall 2020. More details in the code.
//   - for exmaple I get Magma Internal Error for x^6 - 2*x^5 + 4*x^3 - 8*x + 8 .
//   bugs in shimura Taniyama, see in tests

////////////////////    
// New Attributes //
////////////////////    

declare attributes IsogenyClassFq : RRC_CMTypes; // a SeqEnum[AlgAssCMType]
declare attributes IsogenyClassFq : RationalSplittingField; // <M,rtsM> the splitting field of Weil polynomial over Q,
                                                            // together with the roots; 
declare attributes IsogenyClassFq : pAdicSplittingField; // as above, but over Qp 
declare attributes IsogenyClassFq : EmbeddingOfSplittingFields; // an embedding from RationalSplittingField to pAdicSplittingField

declare attributes AlgAssCMType : pAdicReflexField; // a subfield of pAdicSplittingFeld corresponding to the reflex field
declare attributes AlgAssCMType : RationalReflexField; // a subfield of RationalSplittingFeld corresponding to the reflex field
declare attributes AlgAssCMType : IsResidueReflexFieldEmbeddable; // a boolean: if k_E subset F_q
declare attributes AlgAssCMType : ShimuraTaniyama; // add descriptior 
declare attributes IsogenyClassFq :ShimuraTaniyamaPrecomputation; // data that does not depend on the CM-type. To avoid recomputation
declare attributes AlgAssCMType : ComplexRoots; // <rtsM,map> where 
                                                // rtsM is a set of roots of h in M:=RationalSplittingField
                                                // and map is an embedding  of M in to CC

///////////////////////    
// Splitting Fields  //
///////////////////////    

intrinsic RationalSplittingField(AVh::IsogenyClassFq : Method:="Pari") -> FldNum,SeqEnum
{ 
    Returns the splitting field over Q of the Weil polynomial of the isogeny class.
    The vararg can be either "Pari" or "Magma" and decides whether the compoutation is outsourced to Pari or not.
}  
    require Method in {"Pari","Magma"} : "the method selected is not recognized" ;
    if not assigned AVh`RationalSplittingField then
        vprintf ResRefCond : "RationalSplittingField\n";
        h:=WeilPolynomial(AVh);
        if Method eq "Pari" then
            try
                vprintf ResRefCond : "outsourcing to pari\n";
                cmd := Sprintf(
                       "{
                       h = Pol(Vecrev(%o),'x); 
                       M = nfsplitting(h,%o);
                       rtsM = concat([ nfisincl(g,M) | g<-Vec(factor(h,1))[1] ]);
                       print1([Vecrev(M),[ Vecrev(t) | t<-rtsM ]])
                       }",
                       Coefficients(h),#GaloisGroup(h)); // Addding the deg of the splitting fields
                                                         // Speeds up the computation
                                                         // Note: nfisincl is vastly faster than nffactor
                s := Pipe("gp -q -D timer=0", cmd);
                s := eval("<" cat s[2..#s-2] cat ">");
                M:=NumberField(Parent(h)!s[1]);

                vprintf ResRefCond,2: "s[2] = %o\n",s[2];
                vprintf ResRefCond,2: "seqs = %o\n",[ #(r cat [ 0 : i in [1..Degree(M)-#r] ]) : r in s[2]];
                rtsM:=[ M ! (r cat [ 0 : i in [1..Degree(M)-#r] ]) : r in s[2]]; // the output of pari might have less coefficients 
                                                                               // if the one of highest degree are =0
                assert #rtsM eq Degree(h);
                assert2 forall{ r : r in rtsM | Evaluate(h,r) eq 0};
                vprintf ResRefCond : "pari output is read by Magma\n";
            catch e
                vprintf ResRefCond,1 : "Pari is not installed/set-up correctly (don't forget to increase parisizemax). We switch to Magma.\n"; 
                vprint ResRefCond,2 : e;
                M,rtsM:=SplittingField(h);
            end try;
        elif Method eq "Magma" then
            M,rtsM:=SplittingField(h);
        end if;
        AVh`RationalSplittingField:=<M,rtsM>;
    end if;
    return AVh`RationalSplittingField[1],AVh`RationalSplittingField[2];
end intrinsic;

intrinsic pAdicSplittingField(AVh::IsogenyClassFq : MinPrecision:=30 ) -> RngLocA,FldPad,Map
{ 
    Returns the splitting field as RngLocA over Qp of the Weil polynomial of the isogeny class, the corresponding FldPad and an isomorphism.
    The vararg MinPrecision sets the minimal precision.
}   
    if not assigned AVh`pAdicSplittingField or MinPrecision gt Precision(PrimeField(AVh`pAdicSplittingField[2])) then
        vprint ResRefCond : "pAdicSplittingField";
        h:=WeilPolynomial(AVh);
        _,p:=IsPrimePower(FiniteField(AVh));
        prec:=MinPrecision;
        repeat
            go:=true;
            try
                Qp:=pAdicField(p,prec);
                hp:=ChangeRing(h,Qp);
                N0:=SplittingField(hp); //this increases the precision automatically.
                Qp:=PrimeField(N0);
                vprintf ResRefCond,2: "Precision(N0)=%o\nPrecision(PrimeField(N0))=%o\n",Precision(N0),Precision(Qp);
                N:=LocalField(Qp,DefiningPolynomial(N0,Qp)); // we use LocalField because we need 
                                                                              // to construct subfields.
                //map:=map< N0->N | x:-> &+[N.1^(i-1)*Eltseq(x)[i] : i in [1..AbsoluteDegree(N0)]] >;
                N0,map:=RamifiedRepresentation(N);
                map:=Inverse(map);
                // TROUBLES for x^8 - 2*x^7 + 6*x^6 - 15*x^5 + 21*x^4 - 45*x^3 + 54*x^2 - 54*x + 81
                // The next asserts cause an infinite loop 
                // I guess in computing the Roots there is some loss of precision
                // assert forall{ r : r in Roots(h,N) | IsWeaklyZero(Evaluate(h,r[1])) };
                // assert forall{ r : r in Roots(h,N0) | IsWeaklyZero(Evaluate(h,map(r[1]))) };
            catch e
                go:=false;
                prec+:=100;
                vprintf ResRefCond : "precision increased to %o\n",prec;
                vprint ResRefCond,2 : e;
            end try;
        until go;
        AVh`pAdicSplittingField:=<N,N0,map>;
    end if;
    return AVh`pAdicSplittingField[1],AVh`pAdicSplittingField[2],AVh`pAdicSplittingField[3];
end intrinsic;

intrinsic EmbeddingOfSplittingFields(AVh::IsogenyClassFq : MinPrecision:=30 , Method:="Pari") -> Map
{ 
    An embedding from RationalSplittingField to pAdicSplittingField.
    The vararg MinPrecision sets the minimal precision.1
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned AVh`EmbeddingOfSplittingFields or MinPrecision gt Precision(BaseRing(Codomain(AVh`EmbeddingOfSplittingFields))) then
        vprint ResRefCond : "EmbeddingOfSplittingFields";
        M,rtsM:=RationalSplittingField(AVh : Method:=Method);
        m:=DefiningPolynomial(M);
        h:=WeilPolynomial(AVh);
        prec:=Max([MinPrecision,SuggestedPrecision(ChangeRing(m,pAdicRing(CharacteristicFiniteField(AVh))))]);
        vprintf ResRefCond : "initial precision %o\n",prec;
        repeat
            go:=true;
            try
                N,N0,map:=pAdicSplittingField(AVh : MinPrecision:=prec);
                test,rr:=HasRoot(m,N0); //HasRoot doesn't seem to complain when the precision is not enough
                assert test;
                assert IsWeaklyZero(Evaluate(m,rr));
                eps:=hom<M->N | [ map(rr)]  >; // a choice of eps:M->N. 
                                               // exists because both M and N are splitting fields 
                //is_root_M:=IsWeaklyZero(Evaluate(m,eps(M.1))); //I am tired of IsWeaklyZero...
                is_root_M:=Valuation(Evaluate(m,eps(M.1))) gt Round(0.95*Precision(N)) ; 
                                // we test that the image of the primitive root 
                                // of M is sent by eps to a root of def poly of M
                //is_root_h:=forall{ rM : rM in rtsM | IsWeaklyZero(Evaluate(h,eps(rM)))};
                is_root_h:=forall{ rM : rM in rtsM | Valuation(Evaluate(h,eps(rM))) gt Round(0.95*Precision(N))};
                                                                                // similarly, we test that the roots of h in M 
                                                                                // are sent to roots of h in N
                assert is_root_M;
                assert is_root_h;
            catch e
                go:=false;
                prec+:=100;
                vprintf ResRefCond,2: "Precision(N0)=%o\nPrecision(PrimeField(N0))=%o\n",Precision(N0),Precision(PrimeField(N0));
                vprintf ResRefCond : "root found %o\n",rr;
                vprint ResRefCond,2 : Valuation(Evaluate(m,eps(M.1)));
                vprint ResRefCond,2 : [ Valuation(Evaluate(h,eps(rM))) : rM in rtsM ];
                vprintf ResRefCond : "precision increased to %o\n",prec;
                vprint ResRefCond,2 : e;
            end try;
        until go;
        AVh`EmbeddingOfSplittingFields:=eps;
    end if;
    return AVh`EmbeddingOfSplittingFields;
end intrinsic;

// OLD 
// intrinsic pAdicSplittingField(AVh::IsogenyClassFq : MinPrecision:=30 ) -> RngLocA,SeqEnum
// { 
//     Returns the splitting field over Qp of the Weil polynomial of the isogeny class. 
//     The vararg MinPrecision sets the minimal precision.
// }   
//     if not assigned AVh`pAdicSplittingField or MinPrecision gt Precision(AVh`pAdicSplittingField[1]) then
//         vprint ResRefCond : "pAdicSplittingField";
//         h:=WeilPolynomial(AVh);
//         _,p:=IsPrimePower(FiniteField(AVh));
//         prec:=MinPrecision;
//         repeat
//             go:=true;
//             try
//                 Zp:=pAdicRing(p,prec);
//                 M:=SplittingField(h,Zp);
//                 N:=LocalField(FieldOfFractions(Zp),DefiningPolynomial(M,Zp)); // we use LocalField because we need 
//                                                                               // to construct subfields.
//                 rtsN:=[ r[1] : r in Roots(h,N) ];
//             catch e
//                 go:=false;
//                 prec +:=50;
//                 vprintf ResRefCond : "precision increased to %o\n",prec;
//                 vprint ResRefCond,2 : e;
//             end try;
//         until go;
//         AVh`pAdicSplittingField:=<N,rtsN>;
//     end if;
//     return AVh`pAdicSplittingField[1],AVh`pAdicSplittingField[2];
// end intrinsic;
// 
// intrinsic EmbeddingOfSplittingFields(AVh::IsogenyClassFq : MinPrecision:=30 , Method:="Pari") -> Map
// { 
//     An embedding from RationalSplittingField to pAdicSplittingField.
//     The vararg MinPrecision sets the minimal precision.
//     The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
// }   
//     if not assigned AVh`EmbeddingOfSplittingFields or MinPrecision gt Precision(Codomain(AVh`EmbeddingOfSplittingFields)) then
//         vprint ResRefCond : "EmbeddingOfSplittingFields";
//         M,rtsM:=RationalSplittingField(AVh : Method:=Method);
//         h:=WeilPolynomial(AVh);
//         prec:=MinPrecision;
//         repeat
//             go:=true;
//             try
//                 N:=pAdicSplittingField(AVh : MinPrecision:=2*prec);
//                
//                 rtsMinN:=[ r[1] : r in Roots(PolynomialRing(N)!DefiningPolynomial(M)) ];
//                 is_root:=false;
//                 // loop over all the roots, hoping to keep the precision down
//                 for rr in rtsMinN do
//                     eps:=hom<M->N | rr >; // a choice of eps:M->N. 
//                                           // exists because both M and N are splitting fields 
//                     is_root_M:=IsWeaklyZero(Evaluate(DefiningPolynomial(M),eps(M.1))); 
//                                     // we test that the image of the primitive root 
//                                     // of M is sent by eps to a root of def poly of M
//                     is_root_h:=forall{ rM : rM in rtsM | IsWeaklyZero(Evaluate(h,eps(rM)))};
//                                                                                     // similarly, we test that the roots of h in M 
//                                                                                     // are sent to roots of h in N
//                     if is_root_M and is_root_h then
//                         break rr;
//                     end if;
//                 end for;
//                 assert is_root_M;
//                 assert is_root_h;
//             catch e
//                 go:=false;
//                 prec+:=100;
//                 vprintf ResRefCond,2 : "failed to verify the bijection between the roots of h:\nPrecision(N)=%o\n",Precision(N);
//                 vprint ResRefCond,2 : Valuation(Evaluate(DefiningPolynomial(M),eps(M.1)));
//                 vprint ResRefCond,2 : [ Valuation(Evaluate(h,eps(rM))) : rM in rtsM ];
//                 vprintf ResRefCond : "precision increased to %o\n",prec;
//                 vprint ResRefCond,2 : e;
//             end try;
//         until go;
//         AVh`EmbeddingOfSplittingFields:=eps;
//     end if;
//     return AVh`EmbeddingOfSplittingFields;
// end intrinsic;

///////////////////////////////    
// ComplexRoots of a CMType  //
///////////////////////////////    

intrinsic ComplexRoots(AVh::IsogenyClassFq , PHI::AlgAssCMType : Method:="Pari" ) -> FldNum,SeqEnum
{
    Returns a set of g=Dimension(AVh) roots of h=WeilPolynomial(AVh) in the M=RationalSplittingField(AVh) and the embedding M->ComplexField() inducing the correspondence.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned PHI`ComplexRoots then
        vprint ResRefCond : "ComplexRoots";
        F:=FrobeniusEndomorphism(AVh)(1);
        deg:=Degree(Parent(F));
        M,rtsM:=RationalSplittingField(AVh : Method:=Method );
        map:=hom<M->ComplexField() | x:->Conjugate(x,1) >;
        pow_bas_L:=[F^(i-1) : i in [1..deg]];
        b:=CMPosElt(PHI);
        assert b eq &+[(Coordinates([b],pow_bas_L)[1,i])*F^(i-1) : i in [1..deg]];
        rtsM_PHI:=[];
        coord_b_pow_bas:=Coordinates([b],pow_bas_L)[1];
        for FM in rtsM do
            bM:=&+[coord_b_pow_bas[i]*FM^(i-1) : i in [1..deg]]; // bM = 'image' of b in M 
            assert2 bM eq -ComplexConjugate(bM); // a lot more expensive than expected
            if Im(map(bM)) gt 0 then  // this is the choice phi_0:M->CC
                                                // which induces a bijection Hom(L,C) <-> rtsM given by
                                                // phi |-> the unique pi_j such that phi_0(pi_j)=phi(pi)
                Append(~rtsM_PHI,FM);
            end if;
            // write b=sum b_k pi^(k-t)
            // phi in PHI iff Im(phi(b))>0 iff Im(sum b_k phi(pi)^(k-1)) >0 iff Im(sum b_k phi_0(pi_j))>0 iff 
            //            iff bM=sum b_k phi_0(pi_j) in rtsM_PHI. 
        end for;
        assert #rtsM_PHI eq deg div 2;
        PHI`ComplexRoots:=<rtsM_PHI,map>;
    end if;
    return PHI`ComplexRoots[1],PHI`ComplexRoots[2];
end intrinsic;

///////////////////////    
// Shimura-Taniyama  //
///////////////////////    

intrinsic ShimuraTaniyama(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30 , Method:="Pari" ) -> BoolElt
{   
    Returns wheter a CM-type satisfies the Shimura-Taniyama formula for the Forbenius of the Isogeny class AVh
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}
    if not assigned PHI`ShimuraTaniyama then
        vprintf ResRefCond : "ShimuraTaniyama\n";
        prec:=MinPrecision;
        if not assigned AVh`ShimuraTaniyamaPrecomputation or 
            MinPrecision gt Precision(BaseRing(AVh`ShimuraTaniyamaPrecomputation[4][1])) then
            repeat
                go:=true;
                try
                    eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec, Method:=Method );
                    // pre-computation, does not depend on PHI. Should be computed only once.
                    q:=FiniteField(AVh);
                    assert assigned AVh`RationalSplittingField;
                    M,rtsM:=RationalSplittingField(AVh); // we do not use Domain(eps), since we need the roots as well.
                    N:=Codomain(eps); 
                    p_fac_h:=[ g[1] : g in Factorization(WeilPolynomial(AVh),BaseRing(N))];
                    L:=UniverseAlgebra(AVh);
                    fac_q_L:=Factorization(q*MaximalOrder(L));
                    primes:=[ P[1] : P in fac_q_L ];
                    vals_q:=[ P[2] : P in fac_q_L ];
                    F:=FrobeniusEndomorphism(AVh)(1);
                    fac_F_L:=Factorization(F*MaximalOrder(L));
                    vals_F:=[  ];
                    hp_fac:=[ ]; //will contain the p adic factors of h sorted according to the bijection with P in primes 
                    RHS_D_P:=[ ]; // den of RHS of ST
                    for P in primes do
                        val_FatP:=[ fac[2] : fac in fac_F_L | fac[1] eq P ];
                        assert #val_FatP in {0,1}; // P either dividies F or not
                        val_FatP:= (#val_FatP eq 1) select val_FatP[1] else 0;
                        Append(~vals_F,val_FatP);
                        LP,mLP:=Completion(P : MinPrecision:=prec );
                        //Pfac:=[ gp : gp in p_fac_h | IsWeaklyZero(Evaluate(gp,mLP(F))) ]; 
                        //      Completion seems to ignore my precision param so IsWeaklyZero doesn't seem to be working
                        // workaround
                            is_zero:=[ Valuation(Evaluate(gp,mLP(F))) : gp in p_fac_h ];
                            max:=Max(is_zero);
                            Pfac:=[ p_fac_h[i] : i in [1..#p_fac_h] | is_zero[i] gt Round(0.95*max) ];
                        // end workaround
                        assert #Pfac eq 1; 
                        Append(~hp_fac,Pfac[1]); // the p adic factor of h corresponding to the prime P
                        // workaround
                            is_zero:=[ Valuation(Evaluate(Pfac[1],eps(r))) : r in rtsM];
                            max:=Max(is_zero);
                            RHS_D:=#[ rtsM[i] : i in [1..#rtsM] | is_zero[i] gt Round(0.95*max) ];
                        // end workaround
                        vprintf ResRefCond,2 : "Pfac[1]=%o\nRHS_D=%o\n",Pfac[1],RHS_D;
                        vprintf ResRefCond,2 : "are roots ?\n%o\n%o\n",[ Valuation(Evaluate(Pfac[1],eps(r))) : r in rtsM],
                                                                       [ IsWeaklyZero(Evaluate(Pfac[1],eps(r))) : r in rtsM];
                        assert RHS_D eq Degree(Pfac[1]);
                        Append(~RHS_D_P,RHS_D);
                    end for;
                    // end-precomputation
                    // we store the output in AVh`ShimuraTaniyamaPrecomputation
                    // < vals_F , vals_q, RHS_D_P , hp_fac >;
                    AVh`ShimuraTaniyamaPrecomputation:=< vals_F , vals_q, RHS_D_P , hp_fac >;
                catch e
                    go:=false;
                    prec +:=100;
                    vprintf ResRefCond : "precision increased to %o\n",prec;
                    vprint ResRefCond,2 : e;
                end try;
            until go;
        else
            eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec , Method:=Method);
            vals_F, vals_q, RHS_D_P, hp_fac := Explode(AVh`ShimuraTaniyamaPrecomputation);
        end if;

        rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
        vprintf ResRefCond : "ComplexRoots = %o",rtsM_PHI;
        ////////////////----Shimura-Taniyama----///////////////////
        st_tests:=[];
        for iP in [1..#vals_F] do
            // workaround
                is_zero:=[ Valuation(Evaluate(hp_fac[iP],eps(r))) : r in rtsM_PHI ];
                max:=Max(is_zero);
                RHS_N:=#[ rtsM_PHI[i] : i in [1..#rtsM_PHI] | is_zero[i] gt Round(0.95*max) ];
            // end workaround
            LHS:=vals_F[iP]/vals_q[iP];
            RHS:=RHS_N/RHS_D_P[iP];
            Append(~st_tests, LHS eq RHS );
        end for;
        st:=&and(st_tests);
        PHI`ShimuraTaniyama:=st;
    end if;
    return PHI`ShimuraTaniyama;
end intrinsic;

//////////////////////////
// RationalReflexField  //
//////////////////////////

intrinsic RationalReflexField(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30, Method:="Pari" ) -> BoolElt
{   
    Returns the reflex field associated to the CM-type as a subfield of RationalSplittingField.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}
    if not assigned PHI`RationalReflexField then
        vprint ResRefCond : "RationalReflexField";
        h:=WeilPolynomial(AVh);
        rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
        M:=Parent(rtsM_PHI[1]); //M:=RationalSplittingField
        h_fac:=[ hi[1] : hi in Factorization(h)];
        gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
        vprintf ResRefCond : "creating subfield ...";
        E:=sub< M | gens_E_inM >;
        vprintf ResRefCond : "...done\n";
        PHI`RationalReflexField:=E;
    end if;
    return PHI`RationalReflexField;
end intrinsic;

///////////////////////
// pAdicReflexField  //
///////////////////////

intrinsic pAdicReflexField(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30, Method:="Pari" ) -> BoolElt
{   
    Returns the reflex field associated to the CM-type as a subfield of pAdicSplittingField.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}
    prec:=MinPrecision;
    if not assigned PHI`pAdicReflexField or MinPrecision gt Precision(BaseRing(PHI`pAdicReflexField)) then
        vprint ResRefCond : "pAdicReflexField";
        repeat
            go:=true;
            try
                h:=WeilPolynomial(AVh);
                eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec , Method:=Method );
                N:=Codomain(eps);
                assert N cmpeq pAdicSplittingField(AVh);
                rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
                h_fac:=[ hi[1] : hi in Factorization(h)];
                gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                gens_E:=[ eps(g) : g in gens_E_inM ];
                vprintf ResRefCond : "creating subfield ...";
                E:=sub< N | gens_E >; // sometimes it seems to trigger Magma Internal Error in 2.25-6 and 2.25.8
                                      // and it is not related to the precision
                vprintf ResRefCond : "...done\n";
                PHI`pAdicReflexField:=E;
            catch e
                go:=false;
                prec +:=100;
                vprintf ResRefCond : "precision increased to %o\n",prec;
                vprint ResRefCond,2 : e;
            end try;
        until go;
    end if;
    return PHI`pAdicReflexField;
end intrinsic;

/////////////////////////////////////    
// IsResidueReflexFieldEmbeddable  //
/////////////////////////////////////

intrinsic IsResidueReflexFieldEmbeddable(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30, Method:="Pari", MethodReflexField:="pAdic") -> BoolElt
{   
    Returns the if the residue field of reflex field associated to the CM-type can be embedded in Fq=FiniteField(AVh).
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
    The vararg MethodReflexField can be either "pAdic" or "Rational" and decides whether the reflex field is computed as a subfield of the pAdicSplittingField or the RationalSplittingField.
}
    require MethodReflexField in {"pAdic","Rational"} : "MethodReflexField should be either pAdic or Rational";
    if not assigned PHI`IsResidueReflexFieldEmbeddable or MinPrecision gt Precision(PrimeField(AVh`pAdicSplittingField[2])) then
        vprintf ResRefCond : "IsResidueReflexFieldEmbeddable\n";
        q:=FiniteField(AVh);
        p:=CharacteristicFiniteField(AVh);
        if MethodReflexField eq "pAdic" then
            N:=pAdicSplittingField(AVh : MinPrecision:=MinPrecision);
            // (early exit on N)
            // Denote the residue field of N by kN. The residue field of any subfield of N is a subfield of kN.
            // Hence, if kN is a subfield of Fq=FiniteField(AVh) then the same is true for the residue fields of
            // the reflex fields.
            // If this happens, we set the marker compute_reflex_fields:=false and skip the computation of the reflex fields 
            // which is the bottleneck of function. In particular refl_fields will be left empty
            if (Ilog(p,q)) mod Ilog(p,#ResidueClassField(N)) eq 0 then
                PHI`IsResidueReflexFieldEmbeddable:=true;
                vprint ResRefCond : "early exit on N";
            else
                vprint ResRefCond : "no early exit on N";
                E:=pAdicReflexField(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method );
                kE:=ResidueClassField(E);
                PHI`IsResidueReflexFieldEmbeddable:=(Ilog(p,q)) mod Ilog(p,#kE) eq 0;
            end if;
        elif MethodReflexField eq "Rational" then
            E:=RationalReflexField(AVh,PHI : Method:=Method);
            pp:=Decomposition(E,p : Al:="Montes");
            res:=[ #ResidueClassField(P[1]) : P in pp ];
            assert #Seqset(res) eq 1; // all primes should have the same res field
            kE:=res[1];
            PHI`IsResidueReflexFieldEmbeddable:=(Ilog(p,q)) mod Ilog(p,kE) eq 0;
        end if;
    end if;
    return PHI`IsResidueReflexFieldEmbeddable;
end intrinsic;

/////////////////////////////////////////////////    
// Chai-Conrad-Oort : Residual reflex condition //
/////////////////////////////////////////////////    

intrinsic ResidualReflexCondition(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30 , Method:="Pari", MethodReflexField:="pAdic") -> BoolElt 
{   
    It returns whether the CMType PHI of the isogeny class AVh satisfies the Residue Reflex Condition (RRC). 
    MinPrecision is the minimum precision to construct the p-adic splitting field (see below).
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.

    Recall that a CMType PHI satisfies RRC if: 
        *) the CM-type satisfies the Shimura-Taniyama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
    We build create Q and Qp-splitting field of the Weil polynomil and hence a bijection between complex and p-adic roots. 
    This allow us to do the tests in the p-adic splitting field, increasing speed.
    The intermediate data is recorded in the attribute RRC_data. See above for a detailed description. 
}
    vprintf ResRefCond : "ResidualReflexConditioni\n";
    st:=ShimuraTaniyama(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method);
    resrefl:=IsResidueReflexFieldEmbeddable(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method, MethodReflexField:=MethodReflexField );
    return st and resrefl;
end intrinsic;


intrinsic ResidualReflexCondition(AVh::IsogenyClassFq : MinPrecision:=30 , Method:="Pari" ) -> SeqEnum[AlgAssCMType]
{   
    It returns the sequence of CMTypes of the isogeny class AVh that satisfy the Residue Reflex Condition (RRC). 
    MinPrecision is the minimum precision to construct the p-adic splitting field (see below).
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.

    Recall that a CMType PHI satisfies RRC if: 
        *) the CM-type satisfies the Shimura-Taniyama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
    We build create Q and Qp-splitting field of the Weil polynomil and hence a bijection between complex and p-adic roots. 
    This allow us to do the tests in the p-adic splitting field, increasing speed.
    The intermediate data is recorded in the attribute RRC_data. See above for a detailed description.
}
    vprintf ResRefCond : "ResidualReflexConditioni\n";
    if not assigned AVh`RRC_CMTypes then
        rrc_cms:=[];
        for PHI in AllCMTypes(AVh) do
            if ResidualReflexCondition(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method)  then
                Append(~rrc_cms,PHI);
            end if;
        end for;
        AVh`RRC_CMTypes:=rrc_cms;
    end if;
    return AVh`RRC_CMTypes;
end intrinsic;

// // TO BE REMOVED, eventually. This intrinsic is superseeded by the above one ResidualReflexCondition, where we have a 
//                               much better control of the Precision (avoiding several bugs). The timings are very similar.
//                               The old version is kept for consultation.
//
// intrinsic CCO_OLD(AVh::IsogenyClassFq : MinPrecision:=30) -> SeqEnum[AlgAssCMType]
// {   
//     It returns the sequence of CMTypes of the isogeny class AVh that satisfy the Residue Reflex Condition (RRC). 
//     MinPrecision is the minimum precision to construct the p-adic splitting field (see below).
// 
//     Recall that a CMType PHI satisfies RRC if: 
//         *) the CM-type satisfies the Shimura-Taniyama formula, and
//         *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
//     We build create Q and Qp-splitting field of the Weil polynomil and hence a bijection between complex and p-adic roots. 
//     This allow us to do the tests in the p-adic splitting field, increasing speed.
//     The intermediate data is recorded in the attribute RRC_data. See above for a detailed description.
// }
//     vprintf ResRefCond : "CCO_OLD\n";
//         q:=FiniteField(AVh);
//         all_cm:=AllCMTypes(AVh);
//         bs:=[ CMPosElt(PHI) : PHI in all_cm ];
//         prec:=MinPrecision;
// 
//         ////////////////----bijection between p-adic and CC roots via SplittingFields----///////////////////
//         L:=Parent(bs[1]);
//         h:=DefiningPolynomial(L);
//         FL:=PrimitiveElement(L);
//         _,p:=IsPrimePower(q);
//         M,rtsM:=SplittingField(h);
//         prec:=Max([prec] cat [Valuation(c,p) : c in Coefficients(h) | c ne 0]);        
//         Zp:=pAdicRing(p,prec);
//         hp:=ChangeRing(h,Zp);
//         prec:=Max([prec,2*SuggestedPrecision(hp),2*SuggestedPrecision(ChangeRing(DefiningPolynomial(M),Zp))]);
//         ChangePrecision(~Zp,prec);
//         hp:=ChangeRing(h,Zp);
//         repeat
//             go:=true;
//             try
//                 np:=DefiningPolynomial(SplittingField(hp),Zp);
//             catch e
//                 prec +:= 50;
//                 ChangePrecision(~Zp,prec);
//                 hp:=ChangeRing(h,Zp);
//                 go:=false;
//                 vprintf ResRefCond : "precision increased to %o\n",prec;
//             end try;
//         until go;
// 
//         fac:=[ g[1] : g in Factorization(hp) ];
//         N:=LocalField(FieldOfFractions(Zp),np);
//         rootM_inN:=Roots(DefiningPolynomial(M),N)[1,1];          // sometimes the precision is not enough ?
//         /* 
//             // alternative to force higher precision. I don't like it.
//             N0:=LocalField(FieldOfFractions(ChangePrecision(Zp,2*prec)),np); // this is defined to force a higher precision 
//                                                                              // in the computation of eps below...
//                                                                              // it is weird and I don't like it.
//             rootM_inN:=N!Eltseq(Roots(DefiningPolynomial(M),N0)[1,1]);
//             // this aproach seems to create problems later in the line
//             // E:=sub< N | gens_E >; //sometimes it seems to crash...
//             // for poly like:
//             // x^6 - x^5 + 2*x^3 - 4*x + 8, x^6 - x^5 + 4*x^4 - 2*x^3 + 8*x^2 - 4*x + 8, x^6 + x^5 - 2*x^3 + 4*x + 8
//             // hence we remove it
//         */
//         eps:=hom<M->N | rootM_inN >; // a choice of M->N. 
//                                      // exists because both M and N are splitting fields 
//                                      
//         vprint ResRefCond : Evaluate(DefiningPolynomial(M),eps(M.1));
//         assert IsWeaklyZero(Evaluate(DefiningPolynomial(M),eps(M.1)));
//         all_resrefl:=[];
//         all_st:=[];
//         facq:=Factorization(q*MaximalOrder(L));
//         primes:=[ P[1] : P in facq ];
//         valsq:=[ P[2] : P in facq ];
//         facFL:=Factorization(FL*MaximalOrder(L));
//         valsFL:=[  ];
//         hp_fac:=[ ];
//         RHS_D_P:=[ ];
//         for P in primes do
//             vFLP:=[ fac[2] : fac in facFL | fac[1] eq P ];
//             assert #vFLP in {0,1};
//             vFLP:= (#vFLP eq 1) select vFLP[1] else 0;
//             Append(~valsFL,vFLP);
//             LP,mLP:=Completion(P : MinPrecision:=prec );
//             Pfac:=[ gp : gp in fac | Valuation(Evaluate(gp,mLP(FL))) gt (prec div 2) ];
//             assert #Pfac eq 1;
//             Append(~hp_fac,Pfac[1]);
//             RHS_D:=#[ r : r in rtsM | Valuation(Evaluate(Pfac[1],eps(r))) gt (prec div 2) ];
//             assert RHS_D eq Degree(Pfac[1]);
//             Append(~RHS_D_P,RHS_D);
//         end for;
//         pow_bas_L:=[FL^(i-1) : i in [1..Degree(h)]];
//         refl_fields:=[];
// 
//         // (early exit on N)
//         // Denote the residue field of N by kN. The residue field of any subfield of N is a subfield of kN.
//         // Hence, if kN is a subfield of Fq=FiniteField(AVh) then the same is true for the residue fields of
//         // the reflex fields.
//         // If this happens, we set the marker compute_reflex_fields:=false and skip the computation of the reflex fields 
//         // which is the bottleneck of function. In particular refl_fields will be left empty
//         if (Ilog(p,q)) mod Ilog(p,#ResidueClassField(N)) eq 0 then
//             compute_reflex_fields:=false;
//             all_resrefl:=[ true : i in [1..#bs] ];
//         else 
//             compute_reflex_fields:=true;
//         end if;
//         vprint ResRefCond : "early exit on N",compute_reflex_fields;
// 
//         // now we loop over all cm-types
//         for b in bs do
//             assert2 b eq &+[(Coordinates([b],pow_bas_L)[1,i])*FL^(i-1) : i in [1..Degree(h)]];
//             rtsM_PHI:=[];
//             for FM in rtsM do
//                 bM:=&+[(Coordinates([b],pow_bas_L)[1,i])*FM^(i-1) : i in [1..Degree(h)]]; // bM = 'image' of b in M 
//                 assert2 bM eq -ComplexConjugate(bM);
//                 if Im(Conjugates(bM)[1]) gt 0 then  // this is the choice phi_0:M->CC
//                                                     // which induces a bijection Hom(L,C) <-> rtsM given by
//                                                     // phi |-> the unique pi_j such that phi_0(pi_j)=phi(pi)
//                     Append(~rtsM_PHI,FM);
//                 end if;
//                 // write b=sum b_k pi^(k-t)
//                 // phi in PHI iff Im(phi(b))>0 iff Im(sum b_k phi(pi)^(k-1)) >0 iff Im(sum b_k phi_0(pi_j))>0 iff 
//                 //            iff bM=sum b_k phi_0(pi_j) in rtsM_PHI. 
//             end for;
//             assert #rtsM_PHI eq Degree(h) div 2;
//             ////////////////----residue field of reflex field, pAdic ----///////////////////
//             if compute_reflex_fields then //check early exit on N: see above.
//                 h_fac:=[ hi[1] : hi in Factorization(h)];
//                 gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
//                 gens_E:=[ eps(g) : g in gens_E_inM ];
//                 E:=sub< N | gens_E >; //sometimes it seems to crash...
//                 resrefl:=(Ilog(p,q)) mod Ilog(p,#ResidueClassField(E))  eq 0;
//                 Append(~refl_fields,E);
//                 Append(~all_resrefl,resrefl);
//             end if;
//             ////////////////----Shimura-Taniyama----///////////////////
//             st_tests:=[];
//             for iP in [1..#primes] do
//                 RHS_N:=#[ r : r in rtsM_PHI | Valuation(Evaluate(hp_fac[iP],eps(r))) gt (prec div 2) ];
//                 LHS:=valsFL[iP]/valsq[iP];
//                 RHS:=RHS_N/RHS_D_P[iP];
//                 Append(~st_tests, LHS eq RHS );
//             end for;
//             st:=&and(st_tests);
//             Append(~all_st,st);
//         end for;
//         RRC_CMTypes:=[ all_cm[i] : i in [1..#all_cm] | all_resrefl[i] and all_st[i] ];
//     return RRC_CMTypes;
// end intrinsic;

/*
// TESTS
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",2);
    SetAssertions(2);
    PP<x>:=PolynomialRing(Integers());
    polys:=[
        (x^4-5*x^3+15*x^2-25*x+25)*(x^4+5*x^3+15*x^2+25*x+25), //early exit on N. fast
        x^6+3*x^4-10*x^3+15*x^2+125, // no early exit on N. takes ~20 minutes
        x^8 - 7*x^7 + 25*x^6 - 63*x^5 + 123*x^4 - 189*x^3 + 225*x^2 - 189*x + 81, // errors fixed
        x^8 - 4*x^7 + 10*x^6 - 24*x^5 + 48*x^4 - 72*x^3 + 90*x^2 - 108*x + 81  // errors fixed
        ];
    for h in polys do
        AVh:=IsogenyClass(h);
        AVh;
        time #ResidualReflexCondition(AVh);
    end for;

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",1);
    PP<x>:=PolynomialRing(Integers());
    // problematic polys
    // Magma Internal Error in V2.25-6, also in 2.25-8, while creating subfield of N
    // need to use MethodReflexField:="Rational"
    polys:=[
        x^6 - 2*x^5 + 4*x^3 - 8*x + 8, 
        x^8 + 2*x^6 + 4*x^4 + 8*x^2 + 16,
        x^8 + 2*x^7 + 2*x^6 - 4*x^4 + 8*x^2 + 16*x + 16,
        x^8 + 3*x^6 + 9*x^4 + 27*x^2 + 81
    ];
    
    for h in polys do
        h;
        AVh:=IsogenyClass(h);
        AVh,pRank(AVh);
        time _:=RationalSplittingField(AVh : Method:="Pari");
        //time _:=pAdicSplittingField(AVh);
        //time _:=EmbeddingOfSplittingFields(AVh);

        cms:=AllCMTypes(AVh);
        for i->PHI in cms do
            i;
            time ShimuraTaniyama(AVh,PHI);
            // time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="pAdic"); //Magma Int Err
            time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="Rational");
        end for;
    end for;


    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    PP<x>:=PolynomialRing(Integers());
    SetVerbose("ResRefCond",2);
    // triggering errors in ShimuraTaniyma. FIXED
    polys:=[
        x^8 - x^6 + 12*x^4 - 9*x^2 + 81,
        x^8 - x^7 - 3*x^5 + 18*x^4 - 9*x^3 - 27*x + 81,
        x^8 - x^7 + x^6 - 12*x^4 + 9*x^2 - 27*x + 81,
        x^8 - x^7 + 3*x^6 + 27*x^2 - 27*x + 81,
        x^8 - x^7 + 3*x^6 - 9*x^5 + 9*x^4 - 27*x^3 + 27*x^2 - 27*x + 81,
        x^8 + 2*x^6 + 3*x^4 + 18*x^2 + 81,
        x^8 + 2*x^6 + 18*x^4 + 18*x^2 + 81,
        x^8 - 2*x^7 + 3*x^6 + 27*x^2 - 54*x + 81,
        x^8 - 2*x^7 + 3*x^6 - 9*x^5 + 18*x^4 - 27*x^3 + 27*x^2 - 54*x + 81,
        x^8 - 2*x^7 + 3*x^6 + 9*x^5 - 18*x^4 + 27*x^3 + 27*x^2 - 54*x + 81,
        x^8 - 2*x^7 + 9*x^6 - 15*x^5 + 39*x^4 - 45*x^3 + 81*x^2 - 54*x + 81,
        x^8 + 5*x^6 - 6*x^5 + 12*x^4 - 18*x^3 + 45*x^2 + 81,
        x^8 + x^7 + 3*x^6 + 27*x^2 + 27*x + 81,
        x^8 + x^7 + 3*x^6 - 9*x^5 - 9*x^4 - 27*x^3 + 27*x^2 + 27*x + 81,
        x^8 + 2*x^7 + 3*x^6 - 9*x^5 - 18*x^4 - 27*x^3 + 27*x^2 + 54*x + 81,
        x^8 + 2*x^7 + 3*x^6 + 9*x^5 + 18*x^4 + 27*x^3 + 27*x^2 + 54*x + 81
    ];
    for h in polys do
        Ih:=IsogenyClass(h);
        all_cm:=AllCMTypes(Ih);
        for PHI in all_cm do
            ShimuraTaniyama(Ih,PHI);
        end for;
    end for;

    // outsourcing computations to pari/gp
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    PP<x>:=PolynomialRing(Integers());
    SetVerbose("ResRefCond",0);
    SetAssertions(1);
    polys:=[
        x^8+16,
        x^8 - 4*x^7 + 10*x^6 - 24*x^5 + 48*x^4 - 72*x^3 + 90*x^2 - 108*x + 81, // irred, small
        x^8 + 2*x^7 + 3*x^6 - 9*x^5 - 18*x^4 - 27*x^3 + 27*x^2 + 54*x + 81, // not irred, small
        x^8 - 2*x^5 - 2*x^4 - 4*x^3 + 16, // deg 192
        x^8 - 2*x^7 + 2*x^5 - 2*x^4 + 4*x^3 - 16*x + 16, // deg 192
        x^8 - 2*x^5 - 4*x^3 + 16, // deg 384, ~5mins
        x^8 - 3*x^7 + 6*x^6 - 10*x^5 + 14*x^4 - 20*x^3 + 24*x^2 - 24*x + 16 // deg 384, ~5mins
        ];

    for h in polys do
        AVh:=IsogenyClass(h);
        "degree of splitting field =", #GaloisGroup(h);
        time _:=RationalSplittingField(AVh);
        time _:=pAdicSplittingField(AVh);
        time _:=EmbeddingOfSplittingFields(AVh);
        time #ResidualReflexCondition(AVh);
    end for;

*/
