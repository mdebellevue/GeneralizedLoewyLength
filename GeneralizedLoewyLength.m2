needsPackage "Depth"    
    
--
-- ll(M) = inf { t | m^t M = 0}    
    
LoewyLength = method()
LoewyLength Ring := R -> (
    if dim R != 0 then error "Ring must be Artinian";
    (degree numerator reduceHilbert hilbertSeries R)#0+1
    )
    -- mm := ideal vars R;
     
LoewyLength Module := M -> (
    if dim M != 0 then error "Module must be Artinian";
    (degree numerator reduceHilbert hilbertSeries M)#0+1
    )      
    
LoewyLength Ideal := I -> (
    R := (ring I)/I;
    LoewyLength R
    )
    -- mm := ideal vars R;
     
