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
		Verbose => false,
		Bound => 1,
		Sparseness => .5,
		Maximal => true
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
	use 'inhomogeneousSystemOfParameters' instead");

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

genericSystemOfParameters Ideal := opts -> I -> (
    if isHomogeneous I then genericSystemOfParameters(codim I, I,
	    Density => opts.Density, 
	    Attempts => opts.Attempts,
	    Verbose => opts.Verbose,
	    Seed => opts.Seed
	)
    else ideal(
	inhomogeneousSystemOfParameters (I, ring I,
	    Attempts => opts.Attempts,
	    Bound => opts.Bound,
	    Sparseness => opts.Sparseness,
	    Maximal => opts.Maximal
	    )
	)
    )

genericSystemOfParameters Ring := opts -> R -> (
    if isHomogeneous R then (
	genericSystemOfParameters(dim R, ideal vars R,
	    Density => opts.Density, 
	    Attempts => opts.Attempts,
	    Verbose => opts.Verbose,
	    Seed => opts.Seed)
	)
    else ideal (
	inhomogeneousSystemOfParameters (ideal vars R, R,
	    Attempts => opts.Attempts,
	    Bound => opts.Bound,
	    Sparseness => opts.Sparseness,
	    Maximal => opts.Maximal
	    )
	)
    )

genericLoewyLength = method()
genericLoewyLength Ring := R -> (
    I := trim ideal gens gb ideal R;
    LoewyLength (R / genericSystemOfParameters R)
    )

generalizedLoewyLength = method(Options => {Attempts => 100})
-- TODO: Add more options (seed, density)
-- TODO: If res field infinite, then no need to do multiple attempts
generalizedLoewyLength Ring := opts -> R -> (
    lengths := for i to opts.Attempts list genericLoewyLength R;
    gllGuess := min lengths;
    ml := max lengths;
    if ml != gllGuess then (
	g := toString flatten entries gens ideal R;
	print(g | " had diffrent lls for different generic sops.");
	print("  They were");
	print(ml);
	print(" and");
	);
    gllGuess
    )
    
isUlrich = method()
isUlrich Ideal := I -> (
    R := ring I;
    m := ideal gens R;
    dim (R/I) == 0 and numgens trim I == multiplicity ideal vars R
    )
    
type = method()
type Module := M -> (
    R := ring M;
    k := coker vars R;
    d := dim M;
    length Ext^d(k,M)
    )
type Ideal := I -> type module I

ulrichIndex = method(Options => true)
ulrichIndex Ring := { MaxPower => "Multiplicity"} >> opts -> R -> (
    -- TODO: Use bifurcation method to increase computation speed for rings of high multiplicity
    if not dim R == 1 then error("Only defined for dimension one rings");
    local maxPower;
    if opts.MaxPower === "Multiplicity" then maxPower = multiplicity ideal vars R - 1 else maxPower = ops.MaxPower;
    m := ideal vars R;
    for i from 1 to maxPower do (
	if isUlrich m^i then return i
	);
    error("MaxPower encountered without obtaining  Index")
    )
    
eliasIndex = method(Options => true)
-- TODO: Can we upper bound by the multiplicity always?
eliasIndex Ring := { MaxPower => "Multiplicity"} >> opts -> R -> (
    if not dim R == 1 then error("Only defined for dimension one rings");
    local maxPower;
    if opts.MaxPower === "Multiplicity" then maxPower = genericLoewyLength R else maxPower = opts.MaxPower;
    m := ideal vars R;
    k := coker vars R;
    for i from 1 to maxPower do (
    -- type(R^1/m^i) will always be 0th ext
	if rank ambient prune Ext^1(k,m^i) == rank ambient prune Ext^0(k,R^1/m^i) then return i
	);
    error("MaxPower encountered without obtaining Elias Index")
    )

genericEliasIndex = method()
genericEliasIndex Ring := R -> (
    -- TODO: Assert that the ring is Cohen Macaulay?
    I := trim ideal gens gb ideal R;
    gSop := genericSystemOfParameters R;
    gSopm1 := ideal drop(flatten entries gens gSop,1);
    eliasIndex (R / gSopm1)
    )

generalizedEliasIndex = method(Options => {Attempts => 100})
-- TODO: Add more options (seed, density)
generalizedEliasIndex Ring := opts -> R -> (
    eliasIndices := for i to opts.Attempts list genericEliasIndex R;
    eliasGuess := min eliasIndices;
    if max eliasIndices != eliasGuess then (
	g := toString flatten entries gens ideal R;
	print(g | "had diffrent lls for different generic sops");
	);
    eliasGuess
    )
 
genericUlrichIndex = method()
genericUlrichIndex Ring := R -> (
    I := trim ideal gens gb ideal R;
    gSop := genericSystemOfParameters R;
    gSopm1 := ideal drop(flatten entries gens gSop,1);
    ulrichIndex (R / gSopm1)
    )
	-- TODO: add code calling nonHomogeneousSystemOfParameters
	

generalizedUlrichIndex = method(Options => {Attempts => 100})
-- TODO: Add more options (seed, density)
generalizedUlrichIndex Ring := opts -> R -> (
    ulrichIndices := for i to opts.Attempts list genericUlrichIndex R;
    ulrichGuess := min ulrichIndices;
    if max ulrichIndices != ulrichGuess then (
	g := toString flatten entries gens ideal R;
	print(g | "had diffrent lls for different generic sops");
	);
    ulrichGuess
    )
 
-- De Stefani Example
kk = QQ
R = kk[x,y,z]/ideal(x^2-y^5,x*y^2+y*z^3-z^5)
-- Not homogeneous though, so our code doesn't work using type/length
-- TODO: Fix this problem by removing call to ``length'' and ``
        
    
-*    
 Conjecture: length ( R / sop ) is minimized for generic SOPs
 Conjecture: ll ( R / sop ) is minimized for generic SOPs    
 Say one has sop_1, sop_2, both randomly chosen (by genericSOP code)
  - If Coef field is finite, it can happen that l(R/sop_1) =/= l(R/sop_2) since there are finitely many linear SOPs 
  - If Coef field is infinite, conjecture would imply l(R/sop_1) = l(R/sop_2) for all randomly chosen sop_1, sop_2
    
Over finite fields F, Affine_F^n is finite.
Any finite set of points {a_1,...a_m} is the zero set of ideal(x - a_1)ideal(x-a_2)...
Then its complement is also open

Idea 1:
 1. write code that, over a finite field, generates ALL Sops
    i.e., 
      1. for each vector v, see if v cdot x = v_1 x_1 + .. + v_n x_n is a regular element
      2. for each regular element v, seek u not in span v s.t. u cdot x is regular in R/(v cdot x)
 2. Compute ll(R/sop) for each sop
 3. Compute probabilities of each ll being attained
 4. Hope that, as p^n -> infty, the probability of the minimum ll being attained over F_{n^p} goes to 1

Idea 2:
 1. Generate lots of ideals over infinite fields
     - issue: random ideals will be either CIs or Artinian
     - verified for Gorenstein ideals with CM associated graded ring by "Homology of Perfect Complexes"
	 1. Theorem 1: R gor and gr CM then each nonzero R module of finite pd satisfies ll M > reg R + 1
	 2. 1.4 is index R = ll R/Rx for any linear super regular sequence (super regular: initial forms are reg seq in gr)
    	    (set of all super regular sequences is Zariski open? - most probably)
     - In one dim case, we're probably good for CM rings by some results by Dao 
     - Want: probabilistic model of ideals that are not CM (or at least not Gor) with positive dimension quotient
 2. For each, run gll code with lots of attempts
 3. See if any are counterexamples
*-    
