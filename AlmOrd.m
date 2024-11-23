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

    overorders_maximal_at_ss:=function(I)
    // given an isogeny class I returns
    // the sequence of overorders S of ZFV whose super-singulr part is maximal.
    // returns also the local-local places of Q[F]
        R:=ZFVOrder(I);
        oo:=OverOrders(R);
        _,PP,_:=PrimesOfZFVAbove_p(I);
        assert #PP eq 1;
        P:=PP[1];
        OO:=MaximalOrder(Algebra(R));
        MM:=PrimesAbove(OO!!P);
        output:=[];
        for S in oo do
        // S is maximal at P iff S_P = O_K,P 
        // iff 1 in (S:O_K)_M for every maximal ideal M of S above P
        // iff (S:O_K) not subseteq M for every M
            C:=OO!!Conductor(S);
            if forall{M : M in MM | not C subset M } then
                Append(~output,S);
            end if;
        end for;
        return output,MM;
    end function;
