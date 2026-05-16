-- ====================================================================
-- Gram relations, cross-ratios, and Hilbert functions over Q(u)[H,V]
-- ====================================================================


safeEvaluateMap = (F) -> (
    S := source F;
    T := target F;
    KK := coefficientRing S;

    -- denominators of images of the generators
    denoms := unique select(
        apply(flatten entries matrix F, f -> denominator f),
        q -> q != 1
    );

    good := false;
    p := null;
    val := null;

    while not good do (
        p = apply(gens T, a -> a => random(KK));

        -- check denominators before evaluating the rational map
        good = all(denoms, q -> sub(q, p) != 0);

        if good then (
            val = sub(matrix F, p);
        );
    );

    val
);

-- ---------------- Ben's functions ---------------

rationalInterpolateComponent = {SamplePoints => null} >> opts -> (deg, A, F) -> (
    S := source F;
    R := target F;
    dom := newRing(S, Degrees => A);
    KK := coefficientRing source F;
    monomialBasis := sub(basis(deg, dom), S);
    pts := if opts.SamplePoints =!= null then opts.SamplePoints
        else for i from 1 to numcols(monomialBasis) list safeEvaluateMap(F);

    evalBasis := matrix flatten for p in pts list entries sub(monomialBasis, p);
    Kmat := gens ker evalBasis;
    flatten entries (monomialBasis * Kmat)
)

rationalComputeComponent = (deg, A, F) -> (

    S := source F;
    R := target F;
    dom := newRing(S, Degrees => A);

    monomialBasis := sub(basis(deg, dom), S);

    evalBasis := F(monomialBasis);
    evalBasis = entries(evalBasis) / (i -> i / numerator) // matrix;
    (mons, coeffs) := coefficients(evalBasis);

    K := sub(gens ker coeffs, coefficientRing(source F));

    return flatten entries (monomialBasis * K);
)

-- Ordered pairs {i,j} with i<j
ijPairs = (n) -> subsets(toList(1..n), 2);

-- V_{ij} = V_{i, i+1, j} 
-- Returns list of (i,j) pairs
VIndices = (n) -> flatten for i in 1..n list (
    ip := if i == n then 1 else i + 1;
    for j in toList(set(1..n) - set{i, ip}) list (i, j)
);

-- Multidegrees in Z^2n 
ijDegs = (n) -> (
    pairs := ijPairs n;
    vIdx := VIndices n;

    -- P_ij has degree e_i + e_j
    pDeg := apply(pairs, ij -> (
        v := new MutableList from toList(2*n:0);
        i := ij#0;
        j := ij#1;
        v#(i-1) = 1;
        v#(j-1) = 1;
        toList v
    ));

    -- H_ij has degree e_i + e_j + f_i + f_j
    hDeg := apply(pairs, ij -> (
        v := new MutableList from toList(2*n:0);
        i := ij#0;
        j := ij#1;
        v#(i-1) = 1;
        v#(j-1) = 1;
        v#(n+i-1) = 1;
        v#(n+j-1) = 1;
        toList v
    ));

    -- V_ij = V_{i,i+1,j} has degree e_i + f_i
    vDeg := apply(vIdx, ij -> (
        v := new MutableList from toList(2*n:0);
        i := ij#0;
        v#(i-1) = 1;
        v#(n+i-1) = 1;
        toList v
    ));

    (pDeg, hDeg, vDeg)
)

-- Set up the polynomial ring K[P, H, V] with multidegrees and 
-- the rational map
setupRing = (n, d, KK) -> (
    R := KK[
        flatten for i in 1..n list for a in 1..d list x_(i,a),
        flatten for i in 1..n list for a in 1..d list z_(i,a)
    ];

    distSq := (i, j) -> sum(1..d, a -> (x_(i,a) - x_(j,a))^2);
    dotZ   := (i, j) -> sum(1..d, a -> z_(i,a) * z_(j,a));
    dotZX  := (k, i, j) -> sum(1..d, a -> z_(k,a) * (x_(i,a) - x_(j,a)));

    pairs := ijPairs n;
    vIdx  := VIndices n;

    pImg := apply(pairs, ij -> -(1/2) * distSq(ij#0, ij#1));
    hImg := apply(pairs, ij -> 
        dotZ(ij#0, ij#1) * distSq(ij#0, ij#1) 
        - 2 * dotZX(ij#0, ij#0, ij#1) * dotZX(ij#1, ij#0, ij#1));
    vImg := apply(vIdx, ij -> (
        i := ij#0; j := ij#1;
        k := if i == n then 1 else i+1;
        num := dotZX(i,i,k) * distSq(i,j) - dotZX(i,i,j) * distSq(i,k);
        den := distSq(j, k);
        num / den));

    pVars := apply(pairs, ij -> P_(ij#0, ij#1));
    hVars := apply(pairs, ij -> H_(ij#0, ij#1));
    vVars := apply(vIdx,  ij -> V_(ij#0, ij#1));
    (pDeg, hDeg, vDeg) := ijDegs n;
    S := KK[pVars | hVars | vVars, Degrees => pDeg | hDeg | vDeg];

    phi := map(frac R, S, pImg | hImg | vImg);
    (S, R, phi))

-- Set up the polynomial ring K[P, H, V] with multidegrees with condition z_i^2 = 0 and 
-- the rational map
setupRingNullZ = (n, d, KK) -> (

    if d < 2 then error "Use d >= 2 for this split null parametrization.";

    R := KK[
        flatten for i in 1..n list for a in 1..d list x_(i,a),
        flatten for i in 1..n list rho_i,
        flatten for i in 1..n list for b in 1..max(0,d-2) list t_(i,b)
    ];

    -- another signature: q(u,v) = u_1 v_1 + ... + u_{d-1} v_{d-1} - u_d v_d
    qdotXX := (i,j) -> (
        sum(1..d-1, a -> (x_(i,a)-x_(j,a))^2)
        - (x_(i,d)-x_(j,d))^2
    );

    T := i -> (
        if d == 2 then 0_R
        else sum(1..d-2, b -> t_(i,b)^2)
    );

    zc := (i,a) -> (
        if d == 2 then (
            if a == 1 then rho_i else rho_i
        )
        else (
            Ti := T i;
            if a <= d-2 then 2*rho_i*t_(i,a)
            else if a == d-1 then rho_i*(1 - Ti)
            else rho_i*(1 + Ti)
        )
    );

    qdotZ := (i,j) -> (
        sum(1..d-1, a -> zc(i,a)*zc(j,a))
        - zc(i,d)*zc(j,d)
    );

    qdotZX := (k,i,j) -> (
        sum(1..d-1, a -> zc(k,a)*(x_(i,a)-x_(j,a)))
        - zc(k,d)*(x_(i,d)-x_(j,d))
    );

    pairs := ijPairs n;
    vIdx  := VIndices n;

    pImg := apply(pairs, ij -> -(1/2) * qdotXX(ij#0, ij#1));

    hImg := apply(pairs, ij ->
        qdotZ(ij#0, ij#1) * qdotXX(ij#0, ij#1)
        - 2 * qdotZX(ij#0, ij#0, ij#1) * qdotZX(ij#1, ij#0, ij#1)
    );

    vImg := apply(vIdx, ij -> (
        i := ij#0;
        j := ij#1;
        k := if i == n then 1 else i+1;
        num := qdotZX(i,i,k) * qdotXX(i,j) - qdotZX(i,i,j) * qdotXX(i,k);
        den := qdotXX(j,k);
        num / den
    ));

    pVars := apply(pairs, ij -> P_(ij#0, ij#1));
    hVars := apply(pairs, ij -> H_(ij#0, ij#1));
    vVars := apply(vIdx,  ij -> V_(ij#0, ij#1));

    (pDeg, hDeg, vDeg) := ijDegs n;

    S := KK[pVars | hVars | vVars, Degrees => pDeg | hDeg | vDeg];

    phi := map(frac R, S, pImg | hImg | vImg);

    (S, R, phi)
)


-- =================================================================
-- 1. GRAM RELATIONS AMONG P, H, V
-- =================================================================

findGramRelations = (n, d, maxTotalDeg) -> (
    KK = QQ;
    (S, R, phi) := setupRingNullZ(n, d, KK);
    A := transpose matrix degrees S;

    allGens := {};
    idealSoFar := ideal(0_S);

    for totalDeg from 2 to maxTotalDeg do (
        << "-- total multidegree " << totalDeg << " --" << endl;
        for deg in compositions(n, totalDeg) do (
            rels := rationalInterpolateComponent(deg, A, phi);
            if #rels > 0 then (
                newRels := select(rels, f -> f % idealSoFar != 0);
                if #newRels > 0 then (
                    << "  s = " << deg << ": " << #newRels << " new relation(s)" << endl;
                    for f in newRels do << "    " << f << endl;
                    allGens = allGens | newRels;
                    idealSoFar = ideal allGens;
                )
            )
        )
    );

    (idealSoFar, allGens))

-- Example 
(I, gen) = findGramRelations(4, 2, 4)

-- =================================================================
-- 2. INTRINSIC TORUS CROSS-RATIOS u_{ijkl}
-- =================================================================
-- The number is binom(n,2) - n 
-- We compute a basis of ker(B) over Z, where B is the n x binom(n,2) incidence matrix of K_n.

incidenceMat = (n) -> (
    pairs := ijPairs n;
    matrix for i in 1..n list 
        for ij in pairs list (if member(i, ij) then 1 else 0))


-- each column is an exponent vector for one
-- cross-ratio, in the column order of ijPairs(n).
crossRatioExponents = (n) -> (
    if n < 4 then return map(ZZ^(binomial(n,2)), ZZ^0, 0);
    B := incidenceMat n;
    mingens kernel B)


-- Print cross-ratios as Laurent monomials in P_{ij}.
displayCrossRatios = (n) -> (
    if n < 4 then (<< "No cross-ratios for n = " << n << "." << endl; return);
    pairs := ijPairs n;
    K := crossRatioExponents n;
    << "Cross-ratios for n = " << n << " ("
       << numColumns K << " cross-ratios:" << endl;
    for c from 0 to numColumns K - 1 do (
        expVec := flatten entries K_{c};
        numStr := "";
        denStr := "";
        for k from 0 to #pairs - 1 do (
            e := expVec#k;
            ij := pairs#k;
            sym := "P_{" | toString(ij#0) | toString(ij#1) | "}";
            if e > 0 then (
                if e == 1 then numStr = numStr | sym
                else numStr = numStr | sym | "^" | toString(e))
            else if e < 0 then (
                if e == -1 then denStr = denStr | sym
                else denStr = denStr | sym | "^" | toString(-e))
        );
        << "  u^(" << c+1 << ") = " << numStr << " / " << denStr << endl))


-- =================================================================
-- 3. HILBERT FUNCTION OF QQ[H, V] / I_{Gram} AT MULTIDEGREE s
-- =================================================================

hilbertGramQuotient = (n, d, s) -> (
    KK := QQ;
    extraSamples := 5;
    numTries := 20;

    pairs := ijPairs n;
    vIdx  := VIndices n;
    (pDeg, hDeg, vDeg) := ijDegs n;

    hVars := apply(pairs, ij -> H_(ij#0, ij#1));
    vVars := apply(vIdx,  ij -> V_(ij#0, ij#1));
    S := KK[hVars | vVars, Degrees => hDeg | vDeg];

    monBasis := basis(s, S);
    N := numColumns monBasis;

    << "N     = " << N << endl;

    if N == 0 then return 0;


    qdotVec := (u, v) -> (
        sum(0..d-2, a -> u#a * v#a) - u#(d-1) * v#(d-1)
    );

    diffVec := (i, j, xVals) -> (
        for a from 0 to d-1 list xVals#(i-1)#a - xVals#(j-1)#a
    );

    local xVals; local ok;
    ok = false;

    for trial from 1 to numTries do (
        xVals = for i from 1 to n list for a from 1 to d list random(KK);
        ok = true;

        for ij in pairs do (
            dx := diffVec(ij#0, ij#1, xVals);
            ds := qdotVec(dx, dx);
            if ds == 0 then ok = false;
        );

        if ok then break;
    );

    if not ok then error "Could not find a generic x-configuration";

    distSq := (i, j) -> (
        dx := diffVec(i, j, xVals);
        qdotVec(dx, dx)
    );

    nullZ := () -> (
        for i from 1 to n list (
            rho := random(KK);

            if d == 2 then (
                {rho, rho}
            )
            else (
                ts := for b from 1 to d-2 list random(KK);
                T := sum(ts, t -> t^2);
                (apply(ts, t -> 2*rho*t)) | {rho*(1-T), rho*(1+T)}
            )
        )
    );

    numEvals := N + extraSamples;
    badRelCount := 0;

    evalRows := for kEval from 1 to numEvals list (
        zVals := nullZ();

        nullCheck := apply(0..n-1, i -> qdotVec(zVals#i, zVals#i));
        if any(nullCheck, a -> a != 0) then (
            error("z is not null: " | toString nullCheck)
        );

        dotZ := (i, j) -> qdotVec(zVals#(i-1), zVals#(j-1));

        dotZX := (kk, i, j) -> (
            dx := diffVec(i, j, xVals);
            qdotVec(zVals#(kk-1), dx)
        );

        hVals := apply(pairs, ij ->
            dotZ(ij#0, ij#1) * distSq(ij#0, ij#1)
            - 2 * dotZX(ij#0, ij#0, ij#1) * dotZX(ij#1, ij#0, ij#1)
        );

        vVals := apply(vIdx, ij -> (
            i := ij#0;
            j := ij#1;
            kk := if i == n then 1 else i+1;

            num := dotZX(i,i,kk) * distSq(i,j)
                   - dotZX(i,i,j) * distSq(i,kk);

            den := distSq(j, kk);

            if den == 0 then error "Unexpected zero V denominator";

            num / den
        ));

        evalMap := map(KK, S, hVals | vVals);

        if n == 3 then (
            rv := evalMap rel3;
            if rv != 0 then (
                badRelCount = badRelCount + 1;
                << "bad relation value at row " << kEval << " : " << rv << endl;
            );
        );

        first entries evalMap(monBasis)
    );

    M := matrix evalRows;
    r := rank M;

    r
)



-- Example 

displayCrossRatios 4;
displayCrossRatios 5;

print hilbertGramQuotient(3, 3, {1, 1, 1});  -- no Gram constraints
print hilbertGramQuotient(3, 3, {2, 2, 2});

print hilbertGramQuotient(4, 3, {2, 2, 2, 2});



