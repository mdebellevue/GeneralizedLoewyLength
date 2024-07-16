Q = ZZ/101[x,y]
N = coker matrix {{x^2,y^2}}
I = ideal {x^2,y^2}
LoewyLength N
LoewyLength I
R = ZZ/101[x,y]/ideal{x^2,y^2}
M = coker matrix {{x}}

R = ZZ/101[x,y]/ideal{x^2+y^3, y*x^2+x^4}
    
R = ZZ/101[x,y]/ideal{y^3,x^2+y^3}

-- Additivity
-- Check for R, S both dim 1 and CM
kk = QQ
R = kk[x,y]/ideal(x^2+y^2);
S = kk[a,b]/ideal(a*b^2);

-- Increasing the dimension
R = kk[x,y,z]/ideal(x^2+y^2);
S = kk[a,b,c]/ideal(a*b^2,a*b*c);
RxS = fiberProduct(R,S);
print("for R:")
generalizedLoewyLength(R)
print("for S:")
generalizedLoewyLength(S)
print("for RxS:")
generalizedLoewyLength(RxS)
    
-- Other generic invariants
for p from 7 to 13 list (
    R := kk[x,y,z]/ideal(x^p+y^p+z^p);
    (generalizedEliasIndex(R,Attempts => 20), generalizedUlrichIndex(R, Attempts => 20))
    )
