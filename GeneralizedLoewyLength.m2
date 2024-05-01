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

genericLoewyLength = method()
genericLoewyLength Ring := R -> LoewyLength (R / genericSystemOfParameters R)

generalizedLoewyLength = method(Options => {Attempts => 100})
-- TODO: Add more options (seed, density)
generalizedLoewyLength Ring := opts -> R -> (
    lengths := for i to opts.Attempts list genericLoewyLength R;
    gllGuess := min lengths;
    if max lengths != gllGuess then (
	g := toString flatten entries gens ideal R;
	print(g | "had diffrent lls for different generic sops")
    gllGuess
    )
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
