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

////////////////////    
// New Attributes //
////////////////////    

declare attributes IsogenyClassFq : RRC_CMTypes; // a SeqEnum[AlgAssCMType]
declare attributes IsogenyClassFq : RationalSplittingField; // <M,rtsM,map>
declare attributes IsogenyClassFq : PowersOfRationalRoots; // powers of rtsM, with factors of h
declare attributes IsogenyClassFq : pAdicSplittingField; // N a FldPad 
declare attributes IsogenyClassFq : EmbeddingOfSplittingFields; // <eps ,eps_rtsM>

declare attributes AlgAssCMType : pAdicReflexField; // a subfield of pAdicSplittingFeld corresponding to the reflex field
declare attributes AlgAssCMType : RationalReflexField; // a subfield of RationalSplittingFeld corresponding to the reflex field
declare attributes AlgAssCMType : IsResidueReflexFieldEmbeddable; // a boolean: if k_E subset F_q
declare attributes AlgAssCMType : ShimuraTaniyama; // a boolean
declare attributes IsogenyClassFq : ShimuraTaniyamaPrecomputation; // data that does not depend on the CM-type. 
                                                                   // To avoid recomputation
declare attributes AlgAssCMType : ComplexRoots; // rtsM_PHI in M

///////////////////////    
// Splitting Fields  //
///////////////////////    

intrinsic RationalSplittingField(AVh::IsogenyClassFq : MethodRationalSplittingField:="Pari", MinComplexPrecision:=100) -> FldNum,SeqEnum,Map
{ 
    Returns the splitting field over Q of the Weil polynomial of the isogeny class together with the roots and an 'approximate' embedding into the Complex numbers (used internally). The precision of the codomain of the embedding is set by the vararg MinComplexPrecision.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation is outsourced to Pari or not.
}  
    require MethodRationalSplittingField in {"Pari","Magma"} : "the method selected is not recognized" ;
    if not assigned AVh`RationalSplittingField  then
        vprintf ResRefCond : "RationalSplittingField: start\n";
        h:=WeilPolynomial(AVh);
        if MethodRationalSplittingField eq "Pari" then
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
                vtime ResRefCond : s := Pipe("gp -q -D timer=0", cmd);
                s := eval("<" cat s[2..#s-2] cat ">");
                M:=NumberField(Parent(h)!s[1]);
                vprintf ResRefCond,2: "s[2] = %o\n",s[2];
                vprintf ResRefCond,2: "seqs = %o\n",[ #(r cat [ 0 : i in [1..Degree(M)-#r] ]) : r in s[2]];
                rtsM:=[ M ! (r cat [ 0 : i in [1..Degree(M)-#r] ]) : r in s[2]]; // the output of pari might have less coefficients 
                                                                               // if the one of highest degree are =0
                assert #rtsM eq Degree(h);
                vprint ResRefCond : "RationalSplittingField: ... Pari output is read by Magma";
            catch e
                vprint ResRefCond : "RationalSplittingField: Pari is not installed/set-up correctly (don't forget to increase parisizemax)."; 
                vprint ResRefCond,2 : e;
            end try;
        elif MethodRationalSplittingField eq "Magma" then
            M,rtsM:=SplittingField(h);
        end if;
        prec:=MinComplexPrecision;
        repeat
            go:=true;
            try 
                vprint ResRefCond : "RationalSplittingField: compute Complex Root : start ...";
                vtime ResRefCond : rtMCC:=Roots(DefiningPolynomial(M),ComplexField(prec))[1,1];
                test_prec:=-prec div 2;
                vtime ResRefCond : assert Abs(Evaluate(DefiningPolynomial(M),rtMCC)) lt 10^-(prec div 2);
                map:=hom<M->ComplexField(prec) | [ rtMCC ] >; // Much faster than Conjugate(M.1,1), less precise hence the asserts. 
                                                              // Used only to check if elts are imaginary pos.
                vprint ResRefCond : "RationalSplittingField: compute Complex Root : ... done";
            catch e
                go:=false;
                prec:=2*prec;
                vprintf ResRefCond : "RationalSplittingField: Complex precision increased to %o\n",prec; 
            end try;
        until go;
        vprint ResRefCond : "RationalSplittingField: checking output : start ...";
        vtime ResRefCond : assert forall{ r : r in rtsM | Abs(Evaluate(h,map(r))) lt 10^test_prec};
                                // Pari nfisincl is bugged for certain polys.
        vprint ResRefCond : "RationalSplittingField: checking output : ... done";
        vprint ResRefCond : "RationalSplittingField: end";
        AVh`RationalSplittingField:=<M,rtsM,map>;
    end if;
    if MinComplexPrecision gt Precision(Codomain(AVh`RationalSplittingField[3])) then
        vprint ResRefCond : "RationalSplittingField: Increasing the precision of the Complex Root : start ...";
        vtime ResRefCond : rtMCC:=Roots(DefiningPolynomial(AVh`RationalSplittingField[1]),ComplexField(MinComplexPrecision))[1,1];
        map:=hom<M->ComplexField(MinComplexPrecision) | [ rtMCC ] >;
        vprint ResRefCond : "RationalSplittingField: Increasing the precision of the Complex Root : ... done";
        AVh`RationalSplittingField[3]:=map;
    end if;
    return Explode(AVh`RationalSplittingField);
end intrinsic;

intrinsic PowersOfRationalRoots(AVh::IsogenyClassFq) -> Tup
{ 
    For each root FM of WeilPolynomial(AVh) in the RationalSplittingField(AVh) it returns a tuple with the powers of FM and the factor of h of which FM is a root of.
}  
    if not assigned AVh`PowersOfRationalRoots then
        vprint ResRefCond : "PowersOfRationalRoots : start";
        M,rtsM,map:=RationalSplittingField(AVh);
        h:=WeilPolynomial(AVh);
        h_fac:=[ g[1] : g in Factorization(h) ];
        rtsM_pow:=[];
        for iFM->FM in rtsM do
            if #h_fac eq 1 then
                h_FM:=h;
            else
                vprintf ResRefCond : "PowersOfRationalRoots : search min poly of the %o-th root : start ... \n",iFM;
                vtime ResRefCond : FMCC:=map(FM);
                vtime ResRefCond : h_FM:=[ g : g in h_fac | Abs(Evaluate(g,FMCC)) lt 10^-(Precision(Codomain(map)) div 2) ];
                assert #h_FM eq 1;
                h_FM:=h_FM[1];
                vprintf ResRefCond : "PowersOfRationalRoots : search min poly of the %o-th root : ... done\n",iFM;
            end if;
            vprintf ResRefCond : "PowersOfRationalRoots : computing powers of the %o-th root : start ... \n",iFM;
            // using Self makes it very efficient!
            vtime ResRefCond : Append(~rtsM_pow,<[ i gt 1 select Self(i-1)*FM else (M!1) : i in [1..Degree(h)]],h_FM>);
            vprintf ResRefCond : "PowersOfRationalRoots : computing powers of the %o-th root : ... done\n",iFM;
        end for;
        vprint ResRefCond : "PowersOfRationalRoots : end";
        AVh`PowersOfRationalRoots:=rtsM_pow;
    end if;
    return  AVh`PowersOfRationalRoots;
end intrinsic;

intrinsic pAdicSplittingField(AVh::IsogenyClassFq : MinpAdicPrecision:=30 ) -> FldPad
{ 
    Returns the splitting field as FldPad over Qp of the Weil polynomial of the isogeny class.
    The vararg MinpAdicPrecision sets the minimal precision.
}   
    if not assigned AVh`pAdicSplittingField or MinpAdicPrecision gt Precision(PrimeField(AVh`pAdicSplittingField)) then
        vprint ResRefCond : "pAdicSplittingField : start";
        h:=WeilPolynomial(AVh);
        _,p:=IsPrimePower(FiniteField(AVh));
        prec:=Max([MinpAdicPrecision,SuggestedPrecision(ChangeRing(h,pAdicRing(p)))]);
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

intrinsic EmbeddingOfSplittingFields(AVh::IsogenyClassFq : MinpAdicPrecision:=30 , MethodRationalSplittingField:="Pari", MinComplexPrecision:=100) -> Map , SeqEnum
{ 
    An embedding from RationalSplittingField to pAdicSplittingField, together with the images of the roots of h.
    The vararg MinpAdicPrecision sets the minimal precision for the construction of the pAdicSplittingField.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned AVh`EmbeddingOfSplittingFields or MinpAdicPrecision gt Precision(PrimeField(Codomain(AVh`EmbeddingOfSplittingFields[1]))) then
        vprint ResRefCond : "EmbeddingOfSplittingFields : start";
        M,rtsM:=RationalSplittingField(AVh : MethodRationalSplittingField:=MethodRationalSplittingField, MinComplexPrecision:=MinComplexPrecision);
        m:=DefiningPolynomial(M);
        h:=WeilPolynomial(AVh);
        prec:=Max([MinpAdicPrecision,SuggestedPrecision(ChangeRing(m,pAdicRing(CharacteristicFiniteField(AVh))))]);
        vprintf ResRefCond : "EmbeddingOfSplittingFields : initial precision %o\n",prec;
        repeat
            go:=true;
            try
                N:=pAdicSplittingField(AVh : MinpAdicPrecision:=prec);
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing a root of M in N : start ...";
                vtime ResRefCond : test,rr:=HasRoot(m,N); //HasRoot doesn't seem to complain when the precision is not enough
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing a root of M in N : ... done";
                assert test;
                // a choice of eps:M->N. 
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing eps : start ...";
                vtime ResRefCond : eps:=hom<M->N | [ rr ] >;
                vtime ResRefCond : eps_M_1:=eps(M.1);
                vtime ResRefCond : eps_rtsM:=[eps(r) : r in rtsM ];
                vprint ResRefCond : "EmbeddingOfSplittingFields : computing eps : ... done";
                //test
                prec_test:=Round(0.95*Precision(PrimeField(N)));
                is_root_M:=Valuation(Evaluate(m,eps_M_1));
                assert is_root_M gt prec_test ; 
                is_root_h:=[ Valuation(Evaluate(h,eps_rtsM[i])) : i in [1..#rtsM] ];
                assert forall{ val : val in is_root_h | val gt prec_test};
            catch e
                go:=false;
                prec:=Precision(PrimeField(N))+100;
                vprintf ResRefCond : "EmbeddingOfSplittingFields : pAdic precision increased to %o\n",prec;
                vprintf ResRefCond,2 : "EmbeddingOfSplittingFields : root found %o\n",rr;
                vprintf ResRefCond,2 : "EmbeddingOfSplittingFields : is_root_M = %o\n",is_root_M;
                vprintf ResRefCond,2 : "EmbeddingOfSplittingFields : is_root_h = %o\n",is_root_h;
                vprint ResRefCond,2 : e;
            end try;
        until go;
        vprint ResRefCond : "EmbeddingOfSplittingFields : end";
        AVh`EmbeddingOfSplittingFields:=< eps , eps_rtsM >;
    end if;
    return Explode(AVh`EmbeddingOfSplittingFields);
end intrinsic;

///////////////////////////////    
// ComplexRoots of a CMType  //
///////////////////////////////    

intrinsic ComplexRoots(AVh::IsogenyClassFq , PHI::AlgAssCMType : MethodRationalSplittingField:="Pari", MinComplexPrecision:=100 ) -> SeqEnum
{
    Returns a sequence containing the powers of g=Dimension(AVh) roots of h=WeilPolynomial(AVh) in the M=RationalSplittingField(AVh).
    The precision of the embedding of M in to the complex numbers is set by the vararg MinComplexPrecision.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.
}   
    if not assigned PHI`ComplexRoots then
        vprint ResRefCond : "ComplexRoots : start";
        F:=FrobeniusEndomorphism(AVh)(1);
        deg:=Degree(Parent(F));
        M,rtsM,map:=RationalSplittingField(AVh : MethodRationalSplittingField:=MethodRationalSplittingField , MinComplexPrecision:=MinComplexPrecision);
        pow_bas_L:=[F^(i-1) : i in [1..deg]];
        b:=CMPosElt(PHI);
        assert b eq &+[(Coordinates([b],pow_bas_L)[1,i])*F^(i-1) : i in [1..deg]];
        rtsM_PHI:=[];
        coord_b_pow_bas:=Coordinates([b],pow_bas_L)[1];
        rtsM_pow:=PowersOfRationalRoots(AVh);
        for FM_pow in rtsM_pow do
            vprint ResRefCond : "ComplexRoots : compute bM : start ...";
            vtime ResRefCond : bM:=&+[coord_b_pow_bas[i]*FM_pow[1][i] : i in [1..deg]]; // bM = 'image' of b in M 
            vprint ResRefCond : "ComplexRoots : compute bM : ...done";
            vprint ResRefCond : "ComplexRoots : compute bMCC : start ...";
            vtime ResRefCond : bMCC:=map(bM); 
            vprint ResRefCond : "ComplexRoots : compute bMCC : ...done";
            repeat
                go:=true;
                try
                    assert Re(bMCC) lt 10^-(Precision(Codomain(map)) div 2);
                catch e
                    go:=false;
                    prec:=Precision(Codomain(map))*2;
                    vprintf ResRefCond : "ComplexRoots : Complex precision increased to %o\n",prec; 
                    vprint ResRefCond : "ComplexRoots : Recomputing complex root of M ..."; 
                    M,rtsM,map:=RationalSplittingField(AVh : MethodRationalSplittingField:=MethodRationalSplittingField , MinComplexPrecision:=prec);
                    vprint ResRefCond : "ComplexRoots : ... done"; 
                end try;
            until go;
                
            if Im(bMCC) gt 0 then   // the choice phi_0:M->CC is determiend by rtMCC
                                    // which induces a bijection Hom(L,C) <-> rtsM given by
                                    // phi |-> the unique pi_j such that phi_0(pi_j)=phi(pi)
                Append(~rtsM_PHI,FM_pow);
            end if;
            // write b=sum b_k pi^(k-t)
            // phi in PHI iff Im(phi(b))>0 iff Im(sum b_k phi(pi)^(k-1)) >0 iff Im(sum b_k phi_0(pi_j))>0 iff 
            //            iff bM=sum b_k phi_0(pi_j) in rtsM_PHI. 
        end for;
        assert #rtsM_PHI eq deg div 2;
        vprint ResRefCond : "ComplexRoots : end";
        PHI`ComplexRoots:=rtsM_PHI;
    end if;
    return PHI`ComplexRoots;
end intrinsic;

///////////////////////    
// Shimura-Taniyama  //
///////////////////////    

intrinsic ShimuraTaniyama(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinpAdicPrecision:=30 , MethodRationalSplittingField:="Pari" ) -> BoolElt
{   
    Returns wheter a CM-type satisfies the Shimura-Taniyama formula for the Forbenius of the Isogeny class AVh
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.
}
    if not assigned PHI`ShimuraTaniyama then
        vprint ResRefCond : "ShimuraTaniyama : start";
        prec:=MinpAdicPrecision;
        if not assigned AVh`ShimuraTaniyamaPrecomputation or 
            MinpAdicPrecision gt Precision(BaseRing(AVh`ShimuraTaniyamaPrecomputation[4][1])) then
            repeat
                go:=true;
                try
                    eps,eps_rtsM:=EmbeddingOfSplittingFields(AVh : MinpAdicPrecision:=prec, MethodRationalSplittingField:=MethodRationalSplittingField );
                    N:=Codomain(eps); 
                    // pre-computation, does not depend on PHI. Should be computed only once.
                    vprint ResRefCond : "ShimuraTaniyama : precomputation : start ...";
                    q:=FiniteField(AVh);
                    assert assigned AVh`RationalSplittingField;
                    M,rtsM:=RationalSplittingField(AVh); // we do not use Domain(eps), since we need the roots as well.
                    p_fac_h:=[ g[1] : g in Factorization(WeilPolynomial(AVh),PrimeField(N))];
                    L:=UniverseAlgebra(AVh);
                    fac_q_L:=Factorization(q*MaximalOrder(L));
                    primes:=[ P[1] : P in fac_q_L ];
                    vprintf ResRefCond : "ShimuraTaniyama : precomputation : #primes %o\n",#primes;
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
                        // the next few lines determine which p-adic factor of h corresponds to a prime P.
                        // I would like to do it directly, without computing the completion.
                        LP,mLP:=Completion(P : MinPrecision:=prec );
                        //Pfac:=[ gp : gp in p_fac_h | IsWeaklyZero(Evaluate(gp,mLP(F))) ]; 
                        //      Completion seems to ignore my precision param so IsWeaklyZero doesn't seem to be working
                        // workaround
                            mLP_F:=mLP(F);
                            is_zero:=[ Valuation(Evaluate(gp,mLP_F)) : gp in p_fac_h ];
                            max:=Round(0.95*Max(is_zero));
                            Pfac:=[ p_fac_h[i] : i in [1..#p_fac_h] | is_zero[i] gt max ];
                        // end workaround
                        assert #Pfac eq 1; 
                        Append(~hp_fac,Pfac[1]); // the p adic factor of h corresponding to the prime P
                        // workaround
                            is_zero:=[ Valuation(Evaluate(Pfac[1],eps_rM)) : eps_rM in eps_rtsM];
                            max:=Round(0.95*Max(is_zero));
                            RHS_D:=#[ rtsM[i] : i in [1..#rtsM] | is_zero[i] gt max ];
                        // end workaround
                        vprintf ResRefCond,2 : "ShimuraTaniyama : precomputation : Pfac[1]=%o\nRHS_D=%o\n",Pfac[1],RHS_D;
                        vprintf ResRefCond,2 : "ShimuraTaniyama : precomputation : are roots ?\n%o\n",is_zero;
                        assert RHS_D eq Degree(Pfac[1]);
                        Append(~RHS_D_P,RHS_D);
                    end for;
                    // end-precomputation
                    // we store the output in AVh`ShimuraTaniyamaPrecomputation
                    // < vals_F , vals_q, RHS_D_P , hp_fac >;
                    vprint ResRefCond : "ShimuraTaniyama : precomputation : ... done";
                    AVh`ShimuraTaniyamaPrecomputation:=< vals_F , vals_q, RHS_D_P , hp_fac >;
                catch e
                    vprint ResRefCond,2 : e;
                    go:=false;
                    prec:=Precision(PrimeField(N))+100;
                    vprintf ResRefCond : "ShimuraTaniyama : pAdic precision increased to %o\n",prec;
                end try;
            until go;
        else
            eps,eps_rtsM:=EmbeddingOfSplittingFields(AVh : MinpAdicPrecision:=prec , MethodRationalSplittingField:=MethodRationalSplittingField);
            vals_F, vals_q, RHS_D_P, hp_fac := Explode(AVh`ShimuraTaniyamaPrecomputation);
        end if;
        M,rtsM:=RationalSplittingField(AVh);
        rtsM_PHI:=ComplexRoots(AVh,PHI : MethodRationalSplittingField:=MethodRationalSplittingField );
        eps_rtsM_PHI:=[ eps_rtsM[Index(rtsM,r[1,2])] : r in rtsM_PHI ]; 
        ////////////////----Shimura-Taniyama----///////////////////
        st_tests:=[];
        for iP in [1..#vals_F] do
            // workaround
                is_zero:=[ Valuation(Evaluate(hp_fac[iP],r)) : r in eps_rtsM_PHI ];
                max:=Round(0.95*Max(is_zero));
                RHS_N:=#[ rtsM_PHI[i] : i in [1..#rtsM_PHI] | is_zero[i] gt max ];
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

///////////////////
// ReflexField  //
//////////////////

intrinsic RationalReflexField(AVh::IsogenyClassFq , PHI::AlgAssCMType : MethodRationalSplittingField:="Pari", MinComplexPrecision:=100 ) -> BoolElt
{   
    Returns the reflex field associated to the CM-type as a subfield of M=RationalSplittingField.
    The varg MinComplexPrecision determines the precision of the embedding of M into the complex numbers.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.
}
    if not assigned PHI`RationalReflexField then
        vprint ResRefCond : "RationalReflexField : start";
        h:=WeilPolynomial(AVh);
        rtsM_PHI:=ComplexRoots(AVh,PHI : MethodRationalSplittingField:=MethodRationalSplittingField, MinComplexPrecision:=MinComplexPrecision ); 
        M:=RationalSplittingField(AVh);
        h_fac:=[ hi[1] : hi in Factorization(h)];
        rstM_pow:=PowersOfRationalRoots(AVh); // already computed in ComplexRoots
        vprint ResRefCond : "RationalReflexField : computing generators : start ...";
        rtsM_PHI_pow:=[ pow : pow in rstM_pow | pow in rtsM_PHI ];
        gens_E_inM:=&cat[ [ &+[ r[j] : r in [ r[1] : r in rtsM_PHI_pow | r[2] eq hi ] ] : j in [1..Degree(hi)] ] : hi in h_fac ];
        //compare with the old method : sanity check
        assert2 gens_E_inM eq &cat[[ &+[ (r[1,2])^i : r in rtsM_PHI | Evaluate(hi,r[1,2]) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
        vprint ResRefCond : "RationalReflexField : computing generators : ... done";
        vprint ResRefCond : "RationalReflexField : creating subfield : start ...";
        E:=sub< M | gens_E_inM >;
        vprint ResRefCond : "RationalReflexField : creating subfield : ... done";
        vprint ResRefCond : "RationalReflexField : end";
        PHI`RationalReflexField:=E;
    end if;
    return PHI`RationalReflexField;
end intrinsic;

coordinates:=function(S, basis)
    basis_matrix := Matrix([ Flat(bb) : bb in basis]);
    elts_matrix := Matrix([ Flat(x) : x in S]);
    coords_matrix := Solution( basis_matrix, elts_matrix);
    coords := [ Eltseq(coords_matrix[i]) : i in [1..Nrows(coords_matrix)] ];
    return coords;
end function;


intrinsic LocalFieldOverPrimeField(N::FldPad) -> RngLocA,Map
{  Given a local field N of type FldPad returns the isomorphic RngLocA over the PrimeField together with an isomorphism. }
    Qp:=PrimeField(N);
    degN:=AbsoluteDegree(N);
    N0:=LocalField(Qp,DefiningPolynomial(N,Qp));
    powN:=[ i gt 1 select Self(i-1)*N.1 else N!1 : i in [1..degN] ];
    powN:=[ Flat(b) : b in powN ];
    basN:=[ b*g : b in Basis(BaseRing(N)) , g in Basis(N) ];
    coord:=[ N0! c : c in coordinates(basN,powN)];
    NtoN0:=map<N->N0 | c:->&+[Flat(c)[i]*coord[i] : i in [1..degN]]>;
    N0toN:=hom<N0->N | [N.1]>;
    map:=map<N->N0 | x:->NtoN0(x) , y:->N0toN(y)>;
    // TEST 
    //  for i in [1..1000] do 
    //      c:=Random(Integers(N)); d:=c@map@@map-c; if not IsWeaklyZero(d) then Valuation(d),Precision(N); end if; 
    //  end for; 
    return N0,map;
end intrinsic;

my_Eltseq:=function(x)
// N0 of type RngLocA. Eltseq(N0!1) has lenght 1, instead of Degree(N). This function fixes the problem.
    N:=Parent(x);
    deg:=Degree(N);
    seq:=Eltseq(x);
    seq cat:=[N!0 : i in [1..deg-#seq]];
    return seq;
end function;

intrinsic pAdicReflexField(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinpAdicPrecision:=30, MethodRationalSplittingField:="Pari", MinComplexPrecision:=100 ) -> FldPad
{   
    Returns the pAdic reflex field associated to the CM-type. 
    It is created as a compositum of the fields generated by the single generators.
    The varg MinComplexPrecision determines the precision of the embedding of M into the complex numbers.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.
}
    prec:=MinpAdicPrecision;
    if not assigned PHI`pAdicReflexField or MinpAdicPrecision gt Precision(PrimeField(PHI`pAdicReflexField)) then
        vprint ResRefCond : "pAdicReflexField : start";
        repeat
            go:=true;
            try
                h:=WeilPolynomial(AVh);
                h_fac:=[ hi[1] : hi in Factorization(h)];
                eps,eps_rtsM:=EmbeddingOfSplittingFields(AVh : MinpAdicPrecision:=prec , 
                        MethodRationalSplittingField:=MethodRationalSplittingField );
                N:=Codomain(eps);
                degN:=AbsoluteDegree(N);
                Qp:=PrimeField(N);
                rtsM_PHI:=ComplexRoots(AVh,PHI : MinComplexPrecision:=MinComplexPrecision); 
                rtsM_pow:=PowersOfRationalRoots(AVh); // already computed in ComplexRoots
                vprint ResRefCond : "pAdicReflexField : computing generators : start ...";
                rtsM_PHI_pow:=[ pow : pow in rtsM_pow | pow in rtsM_PHI ];
                gens_E_inM:=&cat[ [ &+[ r[j] : r in [ r[1] : r in rtsM_PHI_pow | r[2] eq hi ] ] : j in [1..Degree(hi)] ] : hi in h_fac ];
                //compare with the old method : sanity check
                assert2 gens_E_inM eq &cat[[ &+[ (r[1,2])^i : r in rtsM_PHI | Evaluate(hi,r[1,2]) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                gens_E:=[ eps(g) : g in gens_E_inM ];
                vprint ResRefCond : "pAdicReflexField : computing generators : ... done";
                gens_E:=[ <g,MinimalPolynomial(g,Qp)> : g in gens_E ];
                gens_E:=[ m : m in gens_E | Degree(m[2]) gt 1];
                assert forall{ m : m in gens_E | Degree(m[2]) le degN};
                if #gens_E eq 0 then
                    E:=Qp;
                elif exists{ m : m in gens_E | Degree(m[2]) eq degN } then
                    E:=N;
                else
                    N0,NtoN0:=LocalFieldOverPrimeField(N);
                    gens_E:=[ NtoN0(g[1]) : g in gens_E ];
                    vprint ResRefCond : "pAdicReflexField : creating subfield : start ...";
                    //if forall{ g : g in gens_E | IsNormal(RamifiedRepresentation(LocalField(Qp,g[2])))} then
                    // normal case: this might take more time to test, but we want to avoid using sub as much as possible
                    // in order to escape Magma Internal Error
                    //      E:=SplittingField( &*[ g[2] : g in gens_E ]);
                    E:=RamifiedRepresentation(sub<N0|[g : g in gens_E]>);
                    vprint ResRefCond : "pAdicReflexField : creating subfield : ...done";
                end if;
                vprint ResRefCond : "pAdicReflexField : end";
                PHI`pAdicReflexField:=E;
            catch e
                go:=false;
                prec :=Precision(PrimeField(Codomain(eps)))+100;
                vprintf ResRefCond : "pAdicReflexField : precision increased to %o\n",prec;
                vprint ResRefCond,2 : e;
            end try;
        until go;
    end if;
    return PHI`pAdicReflexField;
end intrinsic;

intrinsic IsResidueReflexFieldEmbeddable(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinpAdicPrecision:=30, MethodRationalSplittingField:="Pari", MethodReflexField:="pAdicEarlyExit", MinComplexPrecision:=100) -> BoolElt
{   
    Returns the if the residue field of reflex field associated to the CM-type can be embedded in Fq=FiniteField(AVh).
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field M and the roots is outsourced to Pari or not.
    The varg MinComplexPrecision determines the precision of the embedding of M into the complex numbers.
    The vararg MethodReflexField can be either "pAdic", "pAdicEarlyExit" or "Rational" and decides whether the reflex field is computed as a subfield of the pAdicSplittingField or the RationalSplittingField.
}
    require MethodReflexField in {"pAdic","pAdicEarlyExit","Rational"} : "MethodReflexField should be either pAdic or Rational";
    if not assigned PHI`IsResidueReflexFieldEmbeddable then
        vprint ResRefCond : "IsResidueReflexFieldEmbeddable : start";
        q:=FiniteField(AVh);
        p:=CharacteristicFiniteField(AVh);
        Ilog_p_q:=Ilog(p,q);
        if MethodReflexField eq "pAdicEarlyExit" then  
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField pAdicEarlyExit";
            eps,eps_rtsM:=EmbeddingOfSplittingFields(AVh : MinpAdicPrecision:=MinpAdicPrecision , MethodRationalSplittingField:=MethodRationalSplittingField , MinComplexPrecision:=MinComplexPrecision );
            N:=Codomain(eps);
            if (Ilog(p,q)) mod Ilog(p,#ResidueClassField(Integers(N))) eq 0 then
                PHI`IsResidueReflexFieldEmbeddable:=true;
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : early exit on N";
            else
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : no early exit on N";
                h:=WeilPolynomial(AVh);
                rtsM_PHI:=ComplexRoots(AVh,PHI : MethodRationalSplittingField:=MethodRationalSplittingField ); 
                h_fac:=[ hi[1] : hi in Factorization(h)];
                rstM_pow:=PowersOfRationalRoots(AVh); // already computed in ComplexRoots
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : computing generators : start ...";
                vtime ResRefCond : rtsM_PHI_pow:=[ pow : pow in rstM_pow | pow in rtsM_PHI ];
                vtime ResRefCond : gens_E_inM:=&cat[ [ &+[ r[j] : r in [ r[1] : r in rtsM_PHI_pow | r[2] eq hi ] ] : j in [1..Degree(hi)] ] : hi in h_fac ];
                //compare with the old method : sanity check
                assert2 gens_E_inM eq &cat[[ &+[ (r[1,2])^i : r in rtsM_PHI | Evaluate(hi,r[1,2]) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                vtime ResRefCond : gens_E:=[ eps(g) : g in gens_E_inM ];
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : computing generators : ... done";
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : start...";
                Qp:=PrimeField(N);
                degN:=Degree(N);
                gens_E:=[ <g,MinimalPolynomial(g,Qp)> : g in gens_E ];
                gens_E:=[ m : m in gens_E | Degree(m[2]) gt 1];
                if #gens_E eq 0 then
                    vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : early exit : E=Qp";
                    E:=Qp;
                    PHI`pAdicReflexField:=E;
                    PHI`IsResidueReflexFieldEmbeddable:=true;
                elif exists{m : m in gens_E | Degree(m[2]) eq degN} then
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : early exit : E=N";
                    E:=N;
                    PHI`pAdicReflexField:=E;
                    PHI`IsResidueReflexFieldEmbeddable:=(AbsoluteInertiaDegree(N) mod Ilog_p_q) eq 0;
                else
                    fld_gens_E:=[ LocalField(Qp,m[2]) : m in gens_E ];
                    if exists{ S : S in fld_gens_E | (InertiaDegree(S) mod Ilog_p_q) eq 0 } then
                        vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : early exit : false on gens_E";
                        PHI`IsResidueReflexFieldEmbeddable:=false;
                    else
//TODO explain why we do normal and not_normal. without this distinction the code would be simpler
                        normal:=[];
                        not_normal:=[];
                        for i->fld in fld_gens_E do
                            S:=RamifiedRepresentation(fld);
                            if IsNormal(S) then
                                Append(~normal,gens_E[i]);
                            else
                                Append(~not_normal,gens_E[i]);
                            end if;
                        end for;
                        gens_added:=[];
                        // normal gens
                        if #normal gt 0 then
                            pol:=normal[1,2];
                            E0:=SplittingField(pol); 
                            if not (AbsoluteInertiaDegree(E0) mod Ilog_p_q) eq 0 then
                                PHI`IsResidueReflexFieldEmbeddable:=false;
                            else
                                for ig->g in normal[2..#normal] do
                                    pol *:=g[2];
                                    E0:=SplittingField(pol); 
                                    Append(~gens_added,g);
                                    is_emb:= (AbsoluteInertiaDegree(E0) mod Ilog_p_q) ;
                                    if not is_emb eq 0 or AbsoluteDegree(E0) eq degN then
                                        PHI`IsResidueReflexFieldEmbeddable:=false;
                                        vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : early exit on intermediate normal field";
                                        break ig;
                                    end if;
                                end for;
                            end if;
                        end if;
                        if (not assigned PHI`IsResidueReflexFieldEmbeddable) and #not_normal gt 0 then
                            // not_normal gens
                            N0,NtoN0:=LocalFieldOverPrimeField(N);
                            E1,E1toN0:=sub<N0 | [ not_normal[1,2] ]>;
                            Append(~gens_added,not_normal[1]);
                            if not (InertiaDegree(E1) mod Ilog_p_q) eq 0 then 
                                PHI`IsResidueReflexFieldEmbeddable:=false;
                            else
                                first_gen:=E1toN0(E1.1);
                                for ig->second_gen in not_normal[2..#not_normal] do
                                    E1,E1toN0:=sub<N0 | [ first_gen,second_gen[2] ]>;
                                    Append(~gens_added,second_gen);
                                    is_emb:= (InertiaDegree(E1) mod Ilog_p_q) ;
                                    if not is_emb or Degree(E1) eq degN then 
                                        PHI`IsResidueReflexFieldEmbeddable:=false;
                                        vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : early exit on intermediate not normal sub field";
                                        break ig;
                                    else
                                        first_gen:=E1toN0(E1.1);
                                    end if;
                                end for;
                            end if;
                        end if;
                        if not assigned PHI`IsResidueReflexFieldEmbeddable then
                            assert #gens_added eq #gens_E; // no early exit has occurred.
                            // put together normal and not_normal
                            if #not_normal eq 0 then
                                //only normal part
                                E:=E0;
                            elif #normal eq 0 then
                                // only not normal part
                                E:=RamifiedRepresentation(E1);
                            else
                                //both
                                test,first_gen:=HasRoot(DefiningPolynomial(E0,Qp));
                                assert test;
                                second_gen:=E1toN0(E1.1);
                                E:=RamifiedRepresentation(sub<N0| [ first_gen,second_gen ]>);
                            end if;
                            E:=PHI`pAdicReflexField; //this is assigned then
                            PHI`IsResidueReflexFieldEmbeddable:=(InertiaDegree(E) mod Ilog_p_q) eq 0;
                        end if;
                        // #gens_added eq #gens_E then we could also assign PHI`pAdiReflexField, but we will have to gen another sub
                        // potentially causing more troubles.
                    end if;
                end if;
                assert assigned PHI`IsResidueReflexFieldEmbeddable;
                vprint ResRefCond : "IsResidueReflexFieldEmbeddable : creating subfield : ... done";
            end if;
        elif MethodReflexField eq "pAdic" then
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField pAdic";
            E:=pAdicReflexField(AVh,PHI : MinpAdicPrecision:=MinpAdicPrecision , MethodRationalSplittingField:=MethodRationalSplittingField );
            kE:=ResidueClassField(Integers(E));
            PHI`IsResidueReflexFieldEmbeddable:=(Ilog_p_q mod Ilog(p,#kE)) eq 0;
        elif MethodReflexField eq "Rational" then
            vprint ResRefCond : "IsResidueReflexFieldEmbeddable : MethodReflexField Rational";
            E:=RationalReflexField(AVh,PHI : MethodRationalSplittingField:=MethodRationalSplittingField);
            pp:=Decomposition(E,p : Al:="Montes");
            res:=[ #ResidueClassField(P[1]) : P in pp ];
            assert #Seqset(res) eq 1; // all primes should have the same res field
            kE:=res[1];
            PHI`IsResidueReflexFieldEmbeddable:=(Ilog_p_q mod Ilog(p,kE)) eq 0;
        end if;
    vprint ResRefCond : "IsResidueReflexFieldEmbeddable : end";
    end if;
    return PHI`IsResidueReflexFieldEmbeddable;
end intrinsic;

/////////////////////////////////////////////////    
// Chai-Conrad-Oort : Residual reflex condition //
/////////////////////////////////////////////////    

intrinsic ResidualReflexCondition(AVh::IsogenyClassFq , PHI::AlgAssCMType : MinpAdicPrecision:=30 , MethodRationalSplittingField:="Pari", MethodReflexField:="pAdicEarlyExit" , MinComplexPrecision:=100) -> BoolElt 
{   
    It returns whether the CMType PHI of the isogeny class AVh satisfies the Residue Reflex Condition (RRC). 
    MinpAdicPrecision is the minimum precision to construct the p-adic splitting field (see below).
    The varg MinComplexPrecision determines the precision of the embedding of M into the complex numbers.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.

    Recall that a CMType PHI satisfies RRC if: 
        *) the CM-type satisfies the Shimura-Taniyama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
    We build create Q and Qp-splitting field of the Weil polynomil and hence a bijection between complex and p-adic roots. 
    This allow us to do the tests in the p-adic splitting field, increasing speed.
    The intermediate data is recorded in the attribute RRC_data. See above for a detailed description. 
}
    vprint ResRefCond : "ResidualReflexCondition : start";
    st:=ShimuraTaniyama(AVh,PHI : MinpAdicPrecision:=MinpAdicPrecision , MethodRationalSplittingField:=MethodRationalSplittingField , MinComplexPrecision:=MinComplexPrecision);
    resrefl:=IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:=MethodReflexField );
    vprint ResRefCond : "ResidualReflexCondition : end";
    return st and resrefl;
end intrinsic;


intrinsic ResidualReflexCondition(AVh::IsogenyClassFq : MinpAdicPrecision:=30 , MethodRationalSplittingField:="Pari", MethodReflexField:="pAdicEarlyExit", MinComplexPrecision:=100 ) -> SeqEnum[AlgAssCMType]
{   
    It returns the sequence of CMTypes of the isogeny class AVh that satisfy the Residue Reflex Condition (RRC). 
    MinpAdicPrecision is the minimum precision to construct the p-adic splitting field (see below).
    The varg MinComplexPrecision determines the precision of the embedding of M into the complex numbers.
    The vararg MethodRationalSplittingField can be either "Pari" or "Magma" and decides whether the computation of the splitting field and the roots is outsourced to Pari or not.

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
            if ResidualReflexCondition(AVh,PHI : MinpAdicPrecision:=MinpAdicPrecision , MethodRationalSplittingField:=MethodRationalSplittingField , MethodReflexField:=MethodReflexField , MinComplexPrecision:=MinComplexPrecision)  then
                Append(~rrc_cms,PHI);
            end if;
        end for;
        AVh`RRC_CMTypes:=rrc_cms;
    end if;
    return AVh`RRC_CMTypes;
end intrinsic;

/*
// TESTS
   
    // very fast test
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",0);
    SetAssertions(2);
    PP<x>:=PolynomialRing(Integers());
    polys:=[
        (x^4-5*x^3+15*x^2-25*x+25)*(x^4+5*x^3+15*x^2+25*x+25),
        x^6+3*x^4-10*x^3+15*x^2+125,
        x^8 - 7*x^7 + 25*x^6 - 63*x^5 + 123*x^4 - 189*x^3 + 225*x^2 - 189*x + 81, // with Rational takes ~20 seconds
        x^8 - 4*x^7 + 10*x^6 - 24*x^5 + 48*x^4 - 72*x^3 + 90*x^2 - 108*x + 81 // too big for Rational
        ];
    for h in polys do
        t0:=Cputime();
        AVh:=IsogenyClass(h);
        AVh;
        "RationalSplittingField";
        time _:=RationalSplittingField(AVh : MethodRationalSplittingField:="Pari");
        "pAdicSplittingField";
        time _:=pAdicSplittingField(AVh);
        "EmbeddingOfSplittingField";
        time _:=EmbeddingOfSplittingFields(AVh);
        cms:=AllCMTypes(AVh);
        for i->PHI in cms do
            i,"th CM type";
            "ShimuraTaniyama";
            time _:=ShimuraTaniyama(AVh,PHI);
            for m in ["pAdicEarlyExit","pAdic"] do
                if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
                "IsResidueReflexFieldEmbeddable with MethodReflexFiedl",m;
                time _:=IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:=m);
            end for;
        end for;
        "tot time",Cputime(t0); 
    end for;

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",2);
    PP<x>:=PolynomialRing(Integers());
    polys:=[
    // all these have the first CM-type giving rise to a non-normal rational reflex feild
    // none of these seem to cause MagmaInternalError
    x^8 - 4*x^7 + 9*x^6 - 16*x^5 + 24*x^4 - 32*x^3 + 36*x^2 - 32*x + 16,
    x^8 - 2*x^7 + x^6 + 4*x^2 - 16*x + 16,
    x^8 - 2*x^7 + x^6 + 4*x^5 - 8*x^4 + 8*x^3 + 4*x^2 - 16*x + 16,
    x^8 - 2*x^7 + 3*x^6 - 4*x^5 + 4*x^4 - 8*x^3 + 12*x^2 - 16*x + 16,
    //x^8 - x^7 + 2*x^6 - 2*x^5 + 2*x^4 - 4*x^3 + 8*x^2 - 8*x + 16,// problems with pAdic. It looks like a Magma bug
                                                                   // MinimalPolynomial(N.1) and MinimalPolynomial(N.1,Qp) 
                                                                   // have the same degree !!!
    //x^8 - x^7 + 2*x^6 + 2*x^5 - 2*x^4 + 4*x^3 + 8*x^2 - 8*x + 16,// problems with pAdic. same as above
    x^8 - x^6 + 4*x^4 - 4*x^2 + 16,
    x^8 + x^6 - 4*x^5 - 8*x^3 + 4*x^2 + 16,
    x^8 + x^6 + 4*x^2 + 16,
    x^8 + x^6 + 4*x^5 + 8*x^3 + 4*x^2 + 16
    ];
    for h in polys do
        h;
        Ih:=IsogenyClass(h);
        PHI:=AllCMTypes(Ih)[1];
        time Er:=RationalReflexField(Ih,PHI);
        "IsNormal Er:",IsNormal(Er);
        if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
        "IsResidueReflexFieldEmbeddable with MethodReflexField Rational";
        time IsResidueReflexFieldEmbeddable(Ih,PHI : MethodReflexField:="Rational");
        time Ep:=pAdicReflexField(Ih,PHI);
        "IsNormal Ep:",IsNormal(Ep);
        if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
        "IsResidueReflexFieldEmbeddable with MethodReflexField pAdic";
        time IsResidueReflexFieldEmbeddable(Ih,PHI : MethodReflexField:="pAdic");
    end for;


    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",2);
    PP<x>:=PolynomialRing(Integers());
    // Magma Internal Error in V2.25-6, also in 2.25-8, with pAdic
    polys:=[
        //x^6 - 2*x^5 + 4*x^3 - 8*x + 8, // Err
        x^8 + 2*x^6 + 4*x^4 + 8*x^2 + 16,
        x^8 + 3*x^6 + 9*x^4 + 27*x^2 + 81 //Magma Int Err
    ];
    for h in polys do
        h;
        AVh:=IsogenyClass(h);
        AVh,pRank(AVh);
        time _:=RationalSplittingField(AVh : MethodRationalSplittingField:="Pari");
        time _:=EmbeddingOfSplittingFields(AVh);

        cms:=AllCMTypes(AVh);
        for i->PHI in cms do
            i;
            time ShimuraTaniyama(AVh,PHI);
            if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
            time IsResidueReflexFieldEmbeddable(AVh,PHI);
            if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
            time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="pAdic");
            if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
            time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="Rational");
        end for;
    end for;


    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    SetVerbose("ResRefCond",0);
    SetAssertions(1);
    PP<x>:=PolynomialRing(Integers());
    h:=x^8 + 2*x^7 + 2*x^6 - 4*x^4 + 8*x^2 + 16*x + 16; // DISAPPEARD by adding an early exit
                                                        // problems with pAdicEarlyExit (error) and pAdic (MagmaInternalError). 
                                                        // ok with Rational
    h;
    AVh:=IsogenyClass(h);
    AVh,pRank(AVh);
    time _:=RationalSplittingField(AVh : MethodRationalSplittingField:="Pari");
    time _:=EmbeddingOfSplittingFields(AVh);
    cms:=AllCMTypes(AVh);
    for i->PHI in cms do
        i;
        time ShimuraTaniyama(AVh,PHI);
        if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
        time IsResidueReflexFieldEmbeddable(AVh,PHI);
        if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
        time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="pAdic");
        if assigned PHI`IsResidueReflexFieldEmbeddable then delete PHI`IsResidueReflexFieldEmbeddable; end if;
        time IsResidueReflexFieldEmbeddable(AVh,PHI : MethodReflexField:="Rational");
    end for;

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");
    PP<x>:=PolynomialRing(Integers());
    SetVerbose("ResRefCond",1);
    // triggering errors in ShimuraTaniyma. FIXED
    // some of this poly trigger the pari bug in nfisincl
    polys:=[
        // x^8 - x^6 + 12*x^4 - 9*x^2 + 81, // Pari bug in nfisincl
        x^8 - x^7 - 3*x^5 + 18*x^4 - 9*x^3 - 27*x + 81,
        x^8 - x^7 + x^6 - 12*x^4 + 9*x^2 - 27*x + 81,
        x^8 - x^7 + 3*x^6 + 27*x^2 - 27*x + 81,
        x^8 - x^7 + 3*x^6 - 9*x^5 + 9*x^4 - 27*x^3 + 27*x^2 - 27*x + 81,
        // x^8 + 2*x^6 + 3*x^4 + 18*x^2 + 81, // Pari bug in nfisincl
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
            time IsResidueReflexFieldEmbeddable(Ih,PHI : MethodReflexField:="pAdic");
        end for;
    end for;

    // slow
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
