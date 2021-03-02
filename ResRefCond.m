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

intrinsic RationalSplittingField(AVh::IsogenyClassFq : Method:="Pari", ComplexPrecision:=100) -> FldNum,SeqEnum
{ 
    Returns the splitting field over Q of the Weil polynomial of the isogeny class.
    The vararg can be either "Pari" or "Magma" and decides whether the compoutation is outsourced to Pari or not.
}  
    require Method in {"Pari","Magma"} : "the method selected is not recognized" ;
    if not assigned AVh`RationalSplittingField  then
        vprintf ResRefCond : "RationalSplittingField: start\n";
        h:=WeilPolynomial(AVh);
        if Method eq "Pari" then
            try
                vprint ResRefCond : "RationalSplittingField: outsourcing to Pari ...";
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
                assert forall{ r : r in rtsM | Evaluate(h,r) eq 0};
                vprint ResRefCond : "RationalSplittingField: ... Pari output is read by Magma";
            catch e
                vprint ResRefCond : "RationalSplittingField: Pari is not installed/set-up correctly, or you endoutered a bug of nfisincl. (don't forget to increase parisizemax)."; 
                vprint ResRefCond : "RationalSplittingField: We switch to Magma"; 
                vprint ResRefCond,2 : e;
                M,rtsM:=SplittingField(h);
            end try;
        elif Method eq "Magma" then
            M,rtsM:=SplittingField(h);
        end if;
        // compute the complex root
        prec:=ComplexPrecision;
        repeat
            go:=true;
            try 
                rtMCC:=Roots(DefiningPolynomial(M),ComplexField(prec))[1,1];
                assert Abs(Evaluate(DefiningPolynomial(M),rtMCC)) lt 10^-(prec div 2);
            catch e
                go:=false;
                prec:=2*prec;
                vprintf ResRefCond : "RationalSplittingField: Complex precision increased to %o\n.",prec; 
            end try;
        until go;
        vprint ResRefCond : "RationalSplittingField: end";
        AVh`RationalSplittingField:=<M,rtsM,rtMCC>;
    end if;
    // do we need more precision?
    if ComplexPrecision gt Precision(AVh`RationalSplittingField[3]) then
        vprint ResRefCond : "RationalSplittingField: Increasing the precision of the Complex Root ...";
        rtMCC:=Roots(DefiningPolynomial(AVh`RationalSplittingField[1]),ComplexField(ComplexPrecision))[1,1];
        vprint ResRefCond : "RationalSplittingField: ... done";
        AVh`RationalSplittingField[3]:=rtMCC;
    end if;
    return Explode(AVh`RationalSplittingField);
end intrinsic;

intrinsic pAdicSplittingField(AVh::IsogenyClassFq : MinPrecision:=30 ) -> FldPad
{ 
    Returns the splitting field as RngLocA over Qp of the Weil polynomial of the isogeny class, the corresponding FldPad and an isomorphism.
    The vararg MinPrecision sets the minimal precision.
}   
    if not assigned AVh`pAdicSplittingField or MinPrecision gt Precision(PrimeField(AVh`pAdicSplittingField)) then
        vprint ResRefCond : "pAdicSplittingField : start";
        h:=WeilPolynomial(AVh);
        _,p:=IsPrimePower(FiniteField(AVh));
        prec:=Max([MinPrecision,SuggestedPrecision(ChangeRing(h,pAdicRing(p)))]);
        repeat
            go:=true;
            try
                hp:=ChangeRing(h,pAdicField(p,prec));
                N:=SplittingField(hp); //this increases the precision automatically.
                assert forall{ r : r in Roots(h,N) | IsWeaklyZero(Evaluate(h,r[1])) };
            catch e
                go:=false;
                prec:=Precision(PrimeField(N))+100;
                vprintf ResRefCond : "pAdicSplittingField : pAdic precision increased to %o\n",prec;
                vprint ResRefCond,2 : e;
            end try;
        until go;
        vprint ResRefCond : "pAdicSplittingField : end";
        AVh`pAdicSplittingField:=N;
    end if;
    return AVh`pAdicSplittingField;
end intrinsic;

intrinsic EmbeddingOfSplittingFields(AVh::IsogenyClassFq : MinPrecision:=30 , Method:="Pari") -> Map
{ 
    An embedding from RationalSplittingField to pAdicSplittingField.
    The vararg MinPrecision sets the minimal precision for the construction of the pAdicSplittingField.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned AVh`EmbeddingOfSplittingFields or MinPrecision gt Precision(PrimeField(Codomain(AVh`EmbeddingOfSplittingFields))) then
        vprint ResRefCond : "EmbeddingOfSplittingFields : start";
        M,rtsM:=RationalSplittingField(AVh : Method:=Method);
        m:=DefiningPolynomial(M);
        h:=WeilPolynomial(AVh);
        prec:=Max([MinPrecision,SuggestedPrecision(ChangeRing(m,pAdicRing(CharacteristicFiniteField(AVh))))]);
        vprintf ResRefCond : "initial precision %o\n",prec;
        repeat
            go:=true;
            try
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing N ...";
                N:=pAdicSplittingField(AVh : MinPrecision:=prec);
                vprint ResRefCond : "EmbeddingOfSplittingFields : ... done";
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing root of M in N ...";
                test,rr:=HasRoot(m,N); //HasRoot doesn't seem to complain when the precision is not enough
                vprint ResRefCond : "EmbeddingOfSplittingFields : ... done";
                assert test;
                assert IsWeaklyZero(Evaluate(m,rr));
                eps:=map<M->N | x:->&+[Eltseq(x)[i]*rr^(i-1) : i in [1..Degree(M)]] >; // a choice of eps:M->N. 
                                               // exists because both M and N are splitting fields 
                //is_root_M:=IsWeaklyZero(Evaluate(m,eps(M.1))); //I am tired of IsWeaklyZero...
                is_root_M:=Valuation(Evaluate(m,eps(M.1))) gt Round(0.95*Precision(PrimeField(N))) ; 
                                // we test that the image of the primitive root 
                                // of M is sent by eps to a root of def poly of M
                //is_root_h:=forall{ rM : rM in rtsM | IsWeaklyZero(Evaluate(h,eps(rM)))};
                is_root_h:=forall{ rM : rM in rtsM | Valuation(Evaluate(h,eps(rM))) gt Round(0.95*Precision(PrimeField(N)))};
                                                                                // similarly, we test that the roots of h in M 
                                                                                // are sent to roots of h in N
                assert is_root_M;
                assert is_root_h;
            catch e
                go:=false;
                prec:=Precision(PrimeField(N))+100;
                vprintf ResRefCond : "EmbeddingOfSplittingFields : pAdic precision increased to %o\n",prec;
                vprintf ResRefCond,2 : "EmbeddingOfSplittingFields : root found %o\n",rr;
                vprint ResRefCond,2 : Valuation(Evaluate(m,eps(M.1)));
                vprint ResRefCond,2 : [ Valuation(Evaluate(h,eps(rM))) : rM in rtsM ];
                vprint ResRefCond,2 : e;
            end try;
        until go;
        vprint ResRefCond : "EmbeddingOfSplittingFields : end";
        AVh`EmbeddingOfSplittingFields:=eps;
    end if;
    return AVh`EmbeddingOfSplittingFields;
end intrinsic;

///////////////////////////////    
// ComplexRoots of a CMType  //
///////////////////////////////    

intrinsic ComplexRoots(AVh::IsogenyClassFq , PHI::AlgAssCMType : Method:="Pari" ) -> FldNum,SeqEnum
{
    Returns a set of g=Dimension(AVh) roots of h=WeilPolynomial(AVh) in the M=RationalSplittingField(AVh) and the embedding M->ComplexField() inducing the correspondence.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned PHI`ComplexRoots then
        vprint ResRefCond : "ComplexRoots : start";
        F:=FrobeniusEndomorphism(AVh)(1);
        deg:=Degree(Parent(F));
        M,rtsM,rtMCC:=RationalSplittingField(AVh : Method:=Method );
        // the next line is not super precise.... 
        // It would be better to use Conjugate(x,1), 
        // but it seems to too slow in certain extreeme cases.
        map:=map<M->ComplexField() | x:->&+[Eltseq(x)[i]*rtMCC^(i-1) : i in [1..Degree(M)]]>;
        pow_bas_L:=[F^(i-1) : i in [1..deg]];
        b:=CMPosElt(PHI);
        assert b eq &+[(Coordinates([b],pow_bas_L)[1,i])*F^(i-1) : i in [1..deg]];
        rtsM_PHI:=[];
        coord_b_pow_bas:=Coordinates([b],pow_bas_L)[1];
        for FM in rtsM do
            bM:=&+[coord_b_pow_bas[i]*FM^(i-1) : i in [1..deg]]; // bM = 'image' of b in M 
            assert2 bM eq -ComplexConjugate(bM); // a lot more expensive than expected
            bMCC:=map(bM); 
            repeat
                go:=true;
                try
                    assert Re(bMCC) lt 10^-(Precision(rtMCC) div 2);
                catch e
                    go:=false;
                    prec:=Precision(rtMCC)*2;
                    vprintf ResRefCond : "ComplexRoots : Complex precision increased to %o\n",prec; 
                    vprint ResRefCond : "ComplexRoots : Recomputing complex root of M ..."; 
                    M,rtsM,rtMCC:=RationalSplittingField(AVh : Method:=Method , ComplexPrecision:=prec);
                    vprint ResRefCond : "ComplexRoots : ... done"; 
                end try;
            until go;
                
            if Im(bMCC) gt 0 then   // the choice phi_0:M->CC is determiend by rtMCC
                                    // which induces a bijection Hom(L,C) <-> rtsM given by
                                    // phi |-> the unique pi_j such that phi_0(pi_j)=phi(pi)
                Append(~rtsM_PHI,FM);
            end if;
            // write b=sum b_k pi^(k-t)
            // phi in PHI iff Im(phi(b))>0 iff Im(sum b_k phi(pi)^(k-1)) >0 iff Im(sum b_k phi_0(pi_j))>0 iff 
            //            iff bM=sum b_k phi_0(pi_j) in rtsM_PHI. 
        end for;
        assert #rtsM_PHI eq deg div 2;
        vprint ResRefCond : "ComplexRoots : end";
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
        vprint ResRefCond : "ShimuraTaniyama : start";
        prec:=MinPrecision;
        if not assigned AVh`ShimuraTaniyamaPrecomputation or 
            MinPrecision gt Precision(BaseRing(AVh`ShimuraTaniyamaPrecomputation[4][1])) then
            repeat
                go:=true;
                try
                    eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec, Method:=Method );
                    // pre-computation, does not depend on PHI. Should be computed only once.
                    vprint ResRefCond : "ShimuraTaniyama : precomputation start";
                    q:=FiniteField(AVh);
                    assert assigned AVh`RationalSplittingField;
                    M,rtsM:=RationalSplittingField(AVh); // we do not use Domain(eps), since we need the roots as well.
                    N:=Codomain(eps); 
                    p_fac_h:=[ g[1] : g in Factorization(WeilPolynomial(AVh),PrimeField(N))];
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
                    vprint ResRefCond : "ShimuraTaniyama : precomputation end";
                    AVh`ShimuraTaniyamaPrecomputation:=< vals_F , vals_q, RHS_D_P , hp_fac >;
                catch e
                    go:=false;
                    prec:=Precision(PrimeField(N))+100;
                    vprintf ResRefCond : "ShimuraTaniyama : pAdic precision increased to %o\n",prec;
                    vprint ResRefCond,2 : e;
                end try;
            until go;
        else
            eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec , Method:=Method);
            vals_F, vals_q, RHS_D_P, hp_fac := Explode(AVh`ShimuraTaniyamaPrecomputation);
        end if;
        rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
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
        vprint ResRefCond : "ShimuraTaniyama : end";
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
        vprint ResRefCond : "RationalReflexField : start";
        h:=WeilPolynomial(AVh);
        rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
        M:=Parent(rtsM_PHI[1]); //M:=RationalSplittingField
        h_fac:=[ hi[1] : hi in Factorization(h)];
        gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
        vprint ResRefCond : "RationalReflexField : creating subfield ...";
        E:=sub< M | gens_E_inM >;
        vprint ResRefCond : "RationalReflexField : ...done";
        vprint ResRefCond : "RationalReflexField : end";
        PHI`RationalReflexField:=E;
    end if;
    return PHI`RationalReflexField;
end intrinsic;

///////////////////////
// pAdicReflexField  //
///////////////////////

intrinsic pAdicReflexField(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30, Method:="Pari" ) -> BoolElt
{   
    Returns the pAdic reflex field associated to the CM-type. 
    It is created as a compositum of the fields generated by the single generators.
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
}
    prec:=MinPrecision;
    if not assigned PHI`pAdicReflexField or MinPrecision gt Precision(PrimeField(PHI`pAdicReflexField)) then
        vprint ResRefCond : "pAdicReflexField : start";
        repeat
            go:=true;
            try
                h:=WeilPolynomial(AVh);
                eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=prec , Method:=Method );
                rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
                h_fac:=[ hi[1] : hi in Factorization(h)];
                gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                gens_E:=[ eps(g) : g in gens_E_inM ];
                vprint ResRefCond : "pAdicReflexField : creating subfield ...";
                Qp:=PrimeField(Codomain(eps));
                min_pols_gens_E:=[ MinimalPolynomial(g,Qp) : g in gens_E ];
                min_pols_gens_E:=[ m : m in min_pols_gens_E | Degree(m) gt 1];
                if #min_pols_gens_E ne 0 then
                    E:=Integers(RamifiedRepresentation(LocalField(Qp,min_pols_gens_E[1])));
                    for m in min_pols_gens_E[2..#min_pols_gens_E ] do
                        E:=Composite(E,Integers(RamifiedRepresentation(LocalField(Qp,m))));
                    end for;
                else
                    E:=Qp;
                end if;
                vprint ResRefCond : "pAdicReflexField : ...done";
                vprint ResRefCond : "pAdicReflexField : end";
                PHI`pAdicReflexField:=E;
            catch e
                go:=false;
                prec :=Precision(PrimeField(Codomain(eps)))+100;
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

intrinsic IsResidueReflexFieldEmbeddable(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30, Method:="Pari", MethodReflexField:="pAdicEarlyExit") -> BoolElt
{   
    Returns the if the residue field of reflex field associated to the CM-type can be embedded in Fq=FiniteField(AVh).
    The vararg Method can be either "Pari" or "Magma" and decides whether the compoutation of the splitting field and the roots is outsourced to Pari or not.
    The vararg MethodReflexField can be either "pAdic", "pAdicEarlyExit" or "Rational" and decides whether the reflex field is computed as a subfield of the pAdicSplittingField or the RationalSplittingField.
}
    require MethodReflexField in {"pAdic","pAdicEarlyExit","Rational"} : "MethodReflexField should be either pAdic or Rational";
    if not assigned PHI`IsResidueReflexFieldEmbeddable then
        vprint ResRefCond : "IsResidueReflexFieldEmbeddable : start";
        q:=FiniteField(AVh);
        p:=CharacteristicFiniteField(AVh);
        if MethodReflexField eq "pAdicEarlyExit" then  
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField pAdicEarlyExit";
            eps:=EmbeddingOfSplittingFields(AVh : MinPrecision:=MinPrecision , Method:=Method );
            N:=Codomain(eps);
            // (early exit on N)
            // Denote the residue field of N by kN. The residue field of any subfield of N is a subfield of kN.
            // Hence, if kN is a subfield of Fq=FiniteField(AVh) then the same is true for the residue fields of
            // the reflex fields.
            // If this happens, we set the marker compute_reflex_fields:=false and skip the computation of the reflex fields 
            // which is the bottleneck of function. In particular refl_fields will be left empty
            if (Ilog(p,q)) mod Ilog(p,#ResidueClassField(Integers(N))) eq 0 then
                PHI`IsResidueReflexFieldEmbeddable:=true;
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : early exit on N";
            else
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : no early exit on N";
                h:=WeilPolynomial(AVh);
                rtsM_PHI:=ComplexRoots(AVh,PHI : Method:=Method ); 
                h_fac:=[ hi[1] : hi in Factorization(h)];
                gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                gens_E:=[ eps(g) : g in gens_E_inM ];
                vprintf ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield ...";
                Qp:=PrimeField(Codomain(eps));
                min_pols_gens_E:=[ MinimalPolynomial(g,Qp) : g in gens_E ];
                min_pols_gens_E:=[ m : m in min_pols_gens_E | Degree(m) gt 1];
                subs:=[ Integers(RamifiedRepresentation(LocalField(Qp,m))) : m in min_pols_gens_E ];
                if exists{ S : S in subs | not (Ilog(p,q)) mod Ilog(p,#ResidueClassField(S)) eq 0 } then
                    vprint ResRefCond : "IsResidueReflexFieldEmbeddable : early exit on gens_E";
                    PHI`IsResidueReflexFieldEmbeddable:=false;
                else
                    if #subs eq 0 then
                        E:=Qp;
                        PHI`IsResidueReflexFieldEmbeddable:=true;
                    else
                        E:=subs[1];
                        for iS in [2..#subs] do
                            E:=Composite(E,subs[iS]);
                            kE:=ResidueClassField(E);
                            if iS eq #subs then
                                PHI`pAdicReflexField:=E;
                            end if;
                            if not (Ilog(p,q)) mod Ilog(p,#kE) eq 0 then
                                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : early exit on intermediate composite";
                                PHI`IsResidueReflexFieldEmbeddable:=false;
                                break iS;
                            end if;
                        end for;
                        if not assigned PHI`IsResidueReflexFieldEmbeddable then
                            // if not assigned then it means that it has not exited earlier with false
                            PHI`IsResidueReflexFieldEmbeddable:=true;
                        end if;
                    end if;
                end if;
            end if;
        elif MethodReflexField eq "pAdic" then
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField pAdic";
            E:=pAdicReflexField(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method );
            kE:=ResidueClassField(E);
            PHI`IsResidueReflexFieldEmbeddable:=(Ilog(p,q) mod Ilog(p,#kE)) eq 0;
    elif MethodReflexField eq "Rational" then
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField Rational";
            E:=RationalReflexField(AVh,PHI : Method:=Method);
            pp:=Decomposition(E,p : Al:="Montes");
            res:=[ #ResidueClassField(P[1]) : P in pp ];
            assert #Seqset(res) eq 1; // all primes should have the same res field
            kE:=res[1];
            PHI`IsResidueReflexFieldEmbeddable:=(Ilog(p,q) mod Ilog(p,kE)) eq 0;
        end if;
    end if;
    vprint ResRefCond : "IsResidueReflexFieldEmbeddable : end";
    return PHI`IsResidueReflexFieldEmbeddable;
end intrinsic;

/////////////////////////////////////////////////    
// Chai-Conrad-Oort : Residual reflex condition //
/////////////////////////////////////////////////    

intrinsic ResidualReflexCondition(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinPrecision:=30 , Method:="Pari", MethodReflexField:="pAdicEarlyExit") -> BoolElt 
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
    vprint ResRefCond : "ResidualReflexCondition : start";
    st:=ShimuraTaniyama(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method);
    resrefl:=IsResidueReflexFieldEmbeddable(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method, MethodReflexField:=MethodReflexField );
    vprint ResRefCond : "ResidualReflexCondition : end";
    return st and resrefl;
end intrinsic;


intrinsic ResidualReflexCondition(AVh::IsogenyClassFq : MinPrecision:=30 , Method:="Pari", MethodReflexField:="pAdicEarlyExit" ) -> SeqEnum[AlgAssCMType]
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
    if not assigned AVh`RRC_CMTypes then
        rrc_cms:=[];
        for PHI in AllCMTypes(AVh) do
            if ResidualReflexCondition(AVh,PHI : MinPrecision:=MinPrecision , Method:=Method , MethodReflexField:=MethodReflexField)  then
                Append(~rrc_cms,PHI);
            end if;
        end for;
        AVh`RRC_CMTypes:=rrc_cms;
    end if;
    return AVh`RRC_CMTypes;
end intrinsic;

/*
// TESTS
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",0);
    SetAssertions(1);
    PP<x>:=PolynomialRing(Integers());
    polys:=[
        (x^4-5*x^3+15*x^2-25*x+25)*(x^4+5*x^3+15*x^2+25*x+25), //early exit on N. fast
        x^6+3*x^4-10*x^3+15*x^2+125, // no early exit on N. takes ~20 minutes. very fast now: 7 secs
        x^8 - 7*x^7 + 25*x^6 - 63*x^5 + 123*x^4 - 189*x^3 + 225*x^2 - 189*x + 81, // errors fixed
        x^8 - 4*x^7 + 10*x^6 - 24*x^5 + 48*x^4 - 72*x^3 + 90*x^2 - 108*x + 81  // errors fixed
        ];
    for h in polys do
        AVh:=IsogenyClass(h);
        AVh;
        time _:=RationalSplittingField(AVh : Method:="Pari");
        time _:=pAdicSplittingField(AVh);
        time _:=EmbeddingOfSplittingFields(AVh);
        time #ResidualReflexCondition(AVh);
    end for;

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",1);
    PP<x>:=PolynomialRing(Integers());
    // FIXED Magma Internal Error in V2.25-6, also in 2.25-8, while creating subfield of N
    polys:=[
        x^6 - 2*x^5 + 4*x^3 - 8*x + 8, 
        x^8 + 2*x^6 + 4*x^4 + 8*x^2 + 16,
        //x^8 + 2*x^7 + 2*x^6 - 4*x^4 + 8*x^2 + 16*x + 16, // problems with pAdicEarlyExit (error) and pAdic (infinite loop). 
                                                         // ok with Rational
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
             time IsResidueReflexFieldEmbeddable(AVh,PHI);
            // time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="pAdic");
            // time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="Rational");
        end for;
    end for;


    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    PP<x>:=PolynomialRing(Integers());
    SetVerbose("ResRefCond",0);
    // triggering errors in ShimuraTaniyma. FIXED
    // some of this poly trigger the pari bug in nfisincl
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
        h;
        Ih:=IsogenyClass(h);
        time M,rtsM:=RationalSplittingField(Ih);
        assert forall{ r : r in rtsM | Evaluate(h,r) eq 0};
        all_cm:=AllCMTypes(Ih);
        for PHI in all_cm do
            time ShimuraTaniyama(Ih,PHI);
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
