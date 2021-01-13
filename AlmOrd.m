/* vim: set syntax=magma : */
/*

    Magma implementation for
        "Polarizations of abelian varieties over finite fields via canonical liftings", 
         by Jonas Bergström, Valentijn Karemaker and Stefano Marseglia.

    Please send bug reports and comments to 
        Stefano Marseglia, stefano.marseglia89@gmail.com


    In this packages we implement the code to compute isomorphism classes of abelian varieties in 
    almost ordinary squarefree isogeny classes over finite fields with odd characteristic.

*/

    is_in_Zp_span:=function( u , gens)
    // given an element u of a RngLocAElt and a sequence gens of RngLocAElt,
    // returns whether u is in the Zp span of gens.
    // this is based on HermiteForm
        assert forall{ g : g in gens | Parent(g) cmpeq Parent(u) };
        Zp:=Integers(BaseRing(Parent(u)));
        gens_u:=gens cat [u];
        den_gens:=Min(&cat[[ Valuation(x) : x in Eltseq(Rows(RepresentationMatrix(g))[1]) ] : g in gens ]);
        den_gens_u:=Min(&cat[[ Valuation(x) : x in Eltseq(Rows(RepresentationMatrix(g))[1]) ] : g in gens_u ]);

        if den_gens ne den_gens_u then
            return false;
        else
            unif:=UniformizingElement(Zp)^(-den_gens);
            gens:=[ unif*g : g in gens ];
            gens_u:=gens cat [unif*u];
            
            gens:=Matrix([ Eltseq(g) : g in gens]);
            hnf_gens:=HermiteForm(ChangeRing(gens,Zp));
            gens_u:=Matrix([ Eltseq(g) : g in gens_u]);
            hnf_gens_u:=HermiteForm(ChangeRing(gens_u,Zp));
            
            // we remove the zero rows
            hnf_gens:=Matrix( [ r : r in Rows(hnf_gens) | exists{ x : x in Eltseq(r) | not IsWeaklyZero(x)} ] );
            hnf_gens_u:=Matrix( [ r : r in Rows(hnf_gens_u) | exists{ x : x in Eltseq(r) | not IsWeaklyZero(x) } ] );
            return hnf_gens eq hnf_gens_u;
        end if;
    end function;

    overorders_maximal_at_ss:=function(I)
    // given an isogeny class I returns
    // the sequence of overorders S whose super-singulr part is maximal.
    // it returns arlso the (quadratic) supersingular part of the algebra
        oo:=FindOverOrders(ZFVOrder(I));
        h:=WeilPolynomial(I);
        g:=Dimension(I);
        q:=FiniteField(I);
        p:=CharacteristicFiniteField(I);

        // we want to factor the polynomial h over Qp.
        // next loop ensures that the precision is big enough
        k:=5;
        repeat
            k+:=1;
            Qp:=pAdicField(p,10*k);
            hp:=ChangeRing(h,Qp);
            fac:=Factorization(hp);
        until SuggestedPrecision(hp) lt k*10 and IsWeaklyEqual(hp,&*[ g[1] : g in fac ]);

        // need to find ss_hp, the p-adic factor of hp that corresponds to the supersingular slope.
        // according to what is written in Oswal-Shankar the constant coeff of ss_hp is equal to q.
        // I check if this characterizes ss_hp.

        Lp:=SplittingField(hp);    
        ss_hp:=[ g[1] : g in fac | Slopes(NewtonPolygon(g[1]))[1]/(Ilog(p,q)) eq -(1/2) ];
        assert #ss_hp eq 1;
        ss_hp:=ss_hp[1]; // this is is the supersingular factor of hp
        assert Degree(ss_hp) eq 2; 
        Kss:=LocalField(BaseRing(ss_hp),ss_hp);
        
        UA:=Algebra(oo[1]);
        F:=PrimitiveElement(UA);
        Fss:=Kss.1;
        Zp:=Integers(BaseRing(Kss));
        uu:=IntegralBasis(Kss)[2];
        mUA_Kss:=map< UA->Kss | t:-> 
            &+[Fss^(j-1)*Coordinates([t],[F^(i-1) : i in [1..Degree(UA)]])[1][j]: j in [1..Degree(UA)]] >;
        output:=[];
        for S in oo do
            // need to check if mUA_Kss(S)\otimes Zp is maximal,
            // that is, if uu in mUA_Kss(S)\otimes Zp            
            zbS:=[ mUA_Kss(z) : z in ZBasis(S) ];
            test:=is_in_Zp_span(uu,zbS);
            ind:=Index(MaximalOrder(UA),S);
            if ind eq 1 then assert test; end if;
            if test then
                Append(~output,S);
            end if;
        end for;
        return output,Kss;
    end function;
