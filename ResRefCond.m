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
        *) the CM-type satisfies the Shimura-Tanyiama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.

*/


declare verbose ResRefCond, 1;


/////////////////////////////////////////////////    
// Chai-Conrad-Oort : Residual reflex condition //
/////////////////////////////////////////////////    

// TODO : 
//   - some precision issues which seem to be triggered by Magma. Reports have been sent in Fall 2020. More details in the code.
//   - for exmaple I get Magma Internal Error for x^6 - 2*x^5 + 4*x^3 - 8*x + 8 .

declare attributes IsogenyClassFq : RRC_CMTypes; // a SeqEnum[AlgAssCMType]
declare attributes IsogenyClassFq : RRC_data; 
            // < all_cm,all_resrefl,all_st,M,rtsM,N,eps,refl_fields >, where
            // - all_cm is the output of AllCMTypes( ) ;
            // - M is a splitting fied over Q of the Weil polynomial h ;
            // - rtsM are the roots of h in M ;
            // - N is a splitting field over Qp of th ;
            // - eps:M->N an embedding ;
            // - refl_fields is the sequence of reflex fields (in N, via eps), constructed from the CM_Types in all_cm;
            // - all_resrefl is a seq of booleans (ordered as all_cm) representing whether the (local) reflex field associated 
            //   to the corresponding CMType has residue field which can be realized as a subfield of Fq=FiniteField(AVh) ;
            // - all_st is a seq of booleans (ordered as all_cm) representing whether the correspoding CMType satisfies the 
            //   the Shimura-Tanyiama formula, where valuations are induced via the embedding eps.

intrinsic ResidualReflexCondition(AVh::IsogenyClassFq : Precision:=30) -> SeqEnum[AlgAssCMType]
{   
    It returns the sequence of CMTypes of the isogeny class AVh that satisfy the Residue Reflex Condition (RRC). 
    Precision is the minimum precision to construct the p-adic splitting field (see below).

    Recall that a CMType PHI satisfies RRC if: 
        *) the CM-type satisfies the Shimura-Tanyiama formula, and
        *) the associated reflex field has residue field that can be realized as a subfield of the field of definition of AVh.
    We build create Q and Qp-splitting field of the Weil polynomil and hence a bijection between complex and p-adic roots. 
    This allow us to do the tests in the p-adic splitting field, increasing speed.
    The intermediate data is recorded in the attribute RRC_data. See above for a detailed description.
}
    vprintf ResRefCond : "ResidualReflexConditioni\n";
    if not assigned AVh`RRC_CMTypes then
        q:=FiniteField(AVh);
        all_cm:=AllCMTypes(AVh);
        bs:=[ CMPosElt(PHI) : PHI in all_cm ];
        prec:=Precision;

        ////////////////----bijection between p-adic and CC roots via SplittingFields----///////////////////
        L:=Parent(bs[1]);
        h:=DefiningPolynomial(L);
        FL:=PrimitiveElement(L);
        _,p:=IsPrimePower(q);
        M,rtsM:=SplittingField(h);
        prec:=Max([prec] cat [Valuation(c,p) : c in Coefficients(h) | c ne 0]);        
        Zp:=pAdicRing(p,prec);
        hp:=ChangeRing(h,Zp);
        prec:=Max([prec,2*SuggestedPrecision(hp),2*SuggestedPrecision(ChangeRing(DefiningPolynomial(M),Zp))]);
        ChangePrecision(~Zp,prec);
        hp:=ChangeRing(h,Zp);
        repeat
            go:=true;
            try
                np:=DefiningPolynomial(SplittingField(hp),Zp);
            catch e
                prec +:= 50;
                ChangePrecision(~Zp,prec);
                hp:=ChangeRing(h,Zp);
                go:=false;
                vprint ResRefCond : "precision increased";
            end try;
        until go;

        fac:=[ g[1] : g in Factorization(hp) ];
        N:=LocalField(FieldOfFractions(Zp),np);
        rootM_inN:=Roots(DefiningPolynomial(M),N)[1,1];          // sometimes the precision is not enough ?
        /* 
            // alternative to force higher precision. I don't like it.
            N0:=LocalField(FieldOfFractions(ChangePrecision(Zp,2*prec)),np); // this is defined to force a higher precision 
                                                                             // in the computation of eps below...
                                                                             // it is weird and I don't like it.
            rootM_inN:=N!Eltseq(Roots(DefiningPolynomial(M),N0)[1,1]);
            // this aproach seems to create problems later in the line
            // E:=sub< N | gens_E >; //sometimes it seems to crash...
            // for poly like:
            // x^6 - x^5 + 2*x^3 - 4*x + 8, x^6 - x^5 + 4*x^4 - 2*x^3 + 8*x^2 - 4*x + 8, x^6 + x^5 - 2*x^3 + 4*x + 8
            // hence we remove it
        */
        eps:=hom<M->N | rootM_inN >; // a choice of M->N. 
                                     // exists because both M and N are splitting fields 
                                     
        vprint ResRefCond : Evaluate(DefiningPolynomial(M),eps(M.1));
        assert IsWeaklyZero(Evaluate(DefiningPolynomial(M),eps(M.1)));
        all_resrefl:=[];
        all_st:=[];
        facq:=Factorization(q*MaximalOrder(L));
        primes:=[ P[1] : P in facq ];
        valsq:=[ P[2] : P in facq ];
        facFL:=Factorization(FL*MaximalOrder(L));
        valsFL:=[  ];
        hp_fac:=[ ];
        RHS_D_P:=[ ];
        for P in primes do
            vFLP:=[ fac[2] : fac in facFL | fac[1] eq P ];
            assert #vFLP in {0,1};
            vFLP:= (#vFLP eq 1) select vFLP[1] else 0;
            Append(~valsFL,vFLP);
            LP,mLP:=Completion(P : Precision:=prec );
            Pfac:=[ gp : gp in fac | Valuation(Evaluate(gp,mLP(FL))) gt (prec div 2) ];
            assert #Pfac eq 1;
            Append(~hp_fac,Pfac[1]);
            RHS_D:=#[ r : r in rtsM | Valuation(Evaluate(Pfac[1],eps(r))) gt (prec div 2) ];
            assert RHS_D eq Degree(Pfac[1]);
            Append(~RHS_D_P,RHS_D);
        end for;
        pow_bas_L:=[FL^(i-1) : i in [1..Degree(h)]];
        refl_fields:=[];

        // (early exit on N)
        // Denote the residue field of N by kN. The residue field of any subfield of N is a subfield of kN.
        // Hence, if kN is a subfield of Fq=FiniteField(AVh) then the same is true for the residue fields of
        // the reflex fields.
        // If this happens, we set the marker compute_reflex_fields:=false and skip the computation of the reflex fields 
        // which is the bottleneck of function. In particular refl_fields will be left empty
        if (Ilog(p,q)) mod Ilog(p,#ResidueClassField(N)) eq 0 then
            compute_reflex_fields:=false;
            all_resrefl:=[ true : i in [1..#bs] ];
        else 
            compute_reflex_fields:=true;
        end if;
        vprint ResRefCond : "early exit on N",compute_reflex_fields;

        // now we loop over all cm-types
        for b in bs do
            assert b eq &+[(Coordinates([b],pow_bas_L)[1,i])*FL^(i-1) : i in [1..Degree(h)]];
            rtsM_PHI:=[];
            for FM in rtsM do
                bM:=&+[(Coordinates([b],pow_bas_L)[1,i])*FM^(i-1) : i in [1..Degree(h)]]; // bM = 'image' of b in M 
                assert bM eq -ComplexConjugate(bM);
                if Im(Conjugates(bM)[1]) gt 0 then  // this is the choice phi_0:M->CC
                                                    // which induces a bijection Hom(L,C) <-> rtsM given by
                                                    // phi |-> the unique pi_j such that phi_0(pi_j)=phi(pi)
                    Append(~rtsM_PHI,FM);
                end if;
                // write b=sum b_k pi^(k-t)
                // phi in PHI iff Im(phi(b))>0 iff Im(sum b_k phi(pi)^(k-1)) >0 iff Im(sum b_k phi_0(pi_j))>0 iff 
                //            iff bM=sum b_k phi_0(pi_j) in rtsM_PHI. 
            end for;
            assert #rtsM_PHI eq Degree(h) div 2;
            ////////////////----residue field of reflex field, pAdic ----///////////////////
            if compute_reflex_fields then //check early exit on N: see above.
                h_fac:=[ hi[1] : hi in Factorization(h)];
                gens_E_inM:=&cat[[ &+[ (r)^i : r in rtsM_PHI | Evaluate(hi,r) eq 0 ] : i in [0..Degree(hi)-1] ] : hi in h_fac];
                gens_E:=[ eps(g) : g in gens_E_inM ];
                E:=sub< N | gens_E >; //sometimes it seems to crash...
                resrefl:=(Ilog(p,q)) mod Ilog(p,#ResidueClassField(E))  eq 0;
                Append(~refl_fields,E);
                Append(~all_resrefl,resrefl);
            end if;
            ////////////////----Shimura-Tanyiama----///////////////////
            st_tests:=[];
            for iP in [1..#primes] do
                RHS_N:=#[ r : r in rtsM_PHI | Valuation(Evaluate(hp_fac[iP],eps(r))) gt (prec div 2) ];
                LHS:=valsFL[iP]/valsq[iP];
                RHS:=RHS_N/RHS_D_P[iP];
                Append(~st_tests, LHS eq RHS );
            end for;
            st:=&and(st_tests);
            Append(~all_st,st);
        end for;
        AVh`RRC_data:=< all_cm,all_resrefl,all_st,M,rtsM,N,eps,refl_fields >;
        AVh`RRC_CMTypes:=[ all_cm[i] : i in [1..#all_cm] | all_resrefl[i] and all_st[i] ];
    end if;
    return AVh`RRC_CMTypes;
end intrinsic;

/*
// TESTS
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    Attach("~/packages_github/PolsAbVarFpCanLift/ResRefCond.m");

    PP<x>:=PolynomialRing(Integers());
    polys:=[
        x^6+3*x^4-10*x^3+15*x^2+125, // no. early exit on N. takes ~20 minutes
        (x^4-5*x^3+15*x^2-25*x+25)*(x^4+5*x^3+15*x^2+25*x+25) //early exit on N. fast
        ];
    for h in polys do
        AVh:=IsogenyClass(h);
        AVh,pRank(AVh);
        q:=FiniteField(AVh);
        all_cm:=AllCMTypes(AVh);
        rrc_cm:=ResidualReflexCondition(AVh);
        [ Index(all_cm,PHI) : PHI in rrc_cm ]; 
        AVh`RRC_data;
    end for;


    AttachSpec("packages/AbVarFq/packages.spec");
    Attach("packages/PolsAbVarFpCanLift/ResRefCond.m");
    PP<x>:=PolynomialRing(Integers());
    // polys that trigger errors
    h:=x^6 - 2*x^5 + 4*x^3 - 8*x + 8; //this give rise to Magma Internal Error in V2.25-6, also in 2.25-8
    h:=x^8 + 2*x^6 + 4*x^4 + 8*x^2 + 16; //this give rise to Magma Internal Error in V2.25-6
    h:=x^8 + 2*x^7 + 2*x^6 - 4*x^4 + 8*x^2 + 16*x + 16;//this give rise to Magma Internal Error in V2.25-6 
    h:=x^8 - 7*x^7 + 25*x^6 - 63*x^5 + 123*x^4 - 189*x^3 + 225*x^2 - 189*x + 81; // broken assert in V2.25-6, also in V2.25-8
    h:=x^8 - 5*x^7 + 10*x^6 - 9*x^5 + 6*x^4 - 27*x^3 + 90*x^2 - 135*x + 81;
    h:=x^8 - 4*x^7 + 10*x^6 - 24*x^5 + 48*x^4 - 72*x^3 + 90*x^2 - 108*x + 81;
    h:=x^8 + 3*x^6 + 9*x^4 + 27*x^2 + 81; // it triggers a different bug in V2.25-8

    try
        AVh:=IsogenyClass(h);
        AVh,pRank(AVh);
        q:=FiniteField(AVh);
        all_cm:=AllCMTypes(AVh);
        rrc_cm:=ResidualReflexCondition(AVh);
        [ Index(all_cm,PHI) : PHI in rrc_cm ]; 
        AVh`RRC_data;
    catch e
        e;
    end try;


*/
