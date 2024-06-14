needsPackage "Pullback"
-- TODO: I hate how pullback returns things
-- Should rewrite it 
fiberProduct = method()
fiberProduct(Ring,Ring):= (R,S) -> (
    assert(coefficientRing R === coefficientRing S);
    k := R/(ideal vars R);
    f := map(k,R);
    g := map(k,S,toList (numgens S : 0));
    (pullback(f,g))#0
    )
    
fiberProduct(Ideal,Ideal) := (I,J) -> ideal fiberProduct((ring I)/I, (ring J)/J)
