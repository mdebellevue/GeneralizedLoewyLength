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
    
genericSystemOfParameters = method(
    Options => {Attempts => 100,
		Density => 0,
		Seed => null,
		Verbose => false
	 }
    )

genericSystemOfParameters(ZZ,Ideal) := opts -> (c,H) ->(
    cd := codim H;
    if c > cd  then error "integer is larger than the codimension of the ideal";

    if numgens H == c then return H;
	--takes care of H = 0 and H principal;    

    I := trim ideal gens gb H;
    if (n := numgens I)<c then error"Ideal has too small codimension.";
    if not isHomogeneous I then error("ideal not homogeneous; 
	use "inhomogeneousSystemOfParameters" instead");

    den := opts.Density;
    att := opts.Attempts;
    sgens := sort (gens trim I, DegreeOrder => Ascending, MonomialOrder => Descending);
    J := opts.Seed;
    if den == 0 then den = ((1+c)/(numcols sgens));
    if opts.Verbose == true then (
	<<"Attempts: "<<att<<" Density: "<< den<<" Seed: "<<J<<endl);
    if J === null then J = ideal 0_(ring I) ;
    if J != 0 and (codim J < numgens J or (gens J)%I != 0) then error"bad Seed ideal";

    K := J;
    c' := 0;
    c'' := 0;

    scan(att, j->(
	    rgens := sgens * random(source sgens, source sgens, Density => 1.0*den);
	    scan(n,i->(
		    c'' = codim(K = J + ideal(rgens_{i}));
		    if c''>c' then(
			J = ideal compress gens K;
			c' = c'';
			if c' == c then break)));
		if opts.Verbose == true then print j;
		if c'==c then break));
    if c' == c then 
    return J else if den == 1 then
	error "no system of parameters found; try increasing Density or Attempts options" else
	genericSystemOfParameters(I, 
	    Density => min(1.0,den+.1), Attempts =>20, Seed =>J, Verbose => opts.Verbose)
    )

genericSystemOfParameters Ideal := opts -> I -> 
    genericSystemOfParameters(codim I, I,
    Density => opts.Density, 
    Attempts => opts.Attempts,
    Verbose => opts.Verbose,
    Seed => opts.Seed)

genericSystemOfParameters Ring := opts -> R ->
    genericSystemOfParameters(dim R, ideal vars R,
    Density => opts.Density, 
    Attempts => opts.Attempts,
    Verbose => opts.Verbose,
    Seed => opts.Seed)




name = method()
name = R -> LoewyLength R / systemOfParameters R
