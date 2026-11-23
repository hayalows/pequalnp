# L-gct-210 upper-bound investigation

The desk statement asks whether every complex linear space L of 5×5 matrices X with per(J+X)=120 has dimension at most 8. These are partial results. The general complex case remains unresolved by this investigation.

## Hessian and two regimes with dimension at most 8

For A a 5×5 matrix let M_k(A) be k! times the sum of the products of size-k matchings. The coefficient of z^k in per(J+zA) is (5−k)! M_k(A)/k!. If A∈L then all M_k(A), k>0, vanish by polynomial uniqueness. Write r_i and c_j for row and column sums, and s for the total. The first two identities are

    M_1 = s,
    M_2 = s² − Σ r_i² − Σ c_j² + Σ A_ij².

On the tangent s=0, the quadratic form q=M_2 is nondegenerate. Indeed, the orthogonal direct sum for the bilinear dot product consists of doubly centered matrices (dimension 16), row-additive matrices with zero total (dimension 4) and column-additive matrices with zero total (dimension 4). Relative to that dot product, q acts by 1, −4 and −4. Its complex Witt bound is 12. If A∈L is doubly centered for all A, the 16-dimensional form gives 8. If L is defined over the reals, the real signature is (16,8), and dimension is also at most 8. Equivalently, the marginal map is injective on any real form of L, since a doubly centered real A with Σ A_ij²=0 is zero.

Every row and column projection of L excludes the vector of ones. If a matrix A in L projects to ones in some row or column, J−A has a zero row or column and would have permanent zero. Thus one can choose normalized annihilators for all ten projections. On the 24-dimensional tangent, a family of functionals vanishing on L whose inverse-Hessian Gram matrix has rank g implies dim L ≤ 12−ceil(g/2): L is isotropic in the common kernel, and the latter has radical equal in dimension to the radical of the Gram form on the span of the functionals. A rank of at least 7 would suffice.

Rank at least 7 does not follow merely from normalizing these ten annihilators. Choose common normals a on all rows and b on all columns, both of squared bilinear norm 1/4 and total sum 1. The row and column Gram blocks each have every entry −1/400. The mixed block is (1/4−b_i)(1/4−a_j)−1/400, by the Kronecker inverse (−I+J/4) ⊗ (−I+J/4) followed by tangent restriction. The rank is at most 3. The explicit choice a=b=(1/4,1/4,1/4,1/4,0) attains 3. These are allowed annihilator data in the absence of further permanent identities, rather than a witness to a dimension-nine level space.

If L has arbitrary common normals on rows and columns, the Hessian on a⊥ is C(v,w)=v⋅w−(Σv)(Σw). The form is nondegenerate unless a⋅a=1/4, in which case the radical is spanned by 1−4a, of total sum 1. The same applies to b⊥. The Hessian in the product ambient b⊥⊗a⊥ is C⊗C. If neither norm is 1/4, the 16-dimensional form is nondegenerate, and its isotropic subspaces already have dimension at most 8. When exactly one norm is exceptional, intersecting the product ambient with the total-zero hyperplane gives a rank-12 form on a 15-dimensional space (radical dimension 3). When both norms are exceptional the analogous rank is 9 (radical dimension 6). These cases give bounds 9 and 10 without cubic information.

For the particularly simple common normal a=b=(1/4,1/4,1/4,1/4,0), a cubic argument does yield 8. In block form X=[A,u;vᵀ,0], the block A is doubly centered 4×4, while u,v are centered four-vectors. The quadratic is Σ A_ij², giving dim image A ≤4. If d=dim L≥9, the kernel U of the A projection has dimension ≥5 in the 6-dimensional vector space of (u,v). The coefficient in M_3(X+zK) of z², with K∈U, is 6 u_Kᵀ A v_K. Its symmetric form on that six-space has rank 2 rank(A) because A annihilates constants on each side. Thus dim U≥5 forces rank A≤1. If dim U=6 then A=0 and d≤6. If dim U=5 then the A-image has dimension ≥4 but consists of rank-at-most-one matrices in a 3×3 matrix space. Such a linear space has a common row or column factor and dimension ≤3. To see the common factor, fix a nonzero rank-one tensor a⊗b in the space. Any other tensor either shares its left or its right factor (otherwise the sum has rank two), and tensors of opposite types with genuinely different factors cannot coexist.

## Cubic Fermat reduction and obstruction at degree four

By inclusion-exclusion over the row and column equality partitions of three labelled factors,

    M_3 = s³ − 3s Σ(r_i²+c_i²) + 3s Σ A_ij²
          + 4Σ A_ij³ − 6Σ A_ij²(r_i+c_j)
          + 6Σ A_ij r_i c_j + 2Σ(r_i³+c_i³).

On s=0, put y_ij=A_ij−(r_i+c_j)/2 and z_m=−3m/10 for each of the ten marginals m=r_i,c_j. Then both vanishing conditions use the same weights:

    M_2   = Σ y_ij² − (125/9) Σ z_m²,
    M_3/4 = Σ y_ij³ − (125/9) Σ z_m³.

These are 35 coordinates, with the last ten equal to the corresponding averages of y. The quadratic-and-cubic Fermat dimension bound extends to arbitrary nonzero weights for which no nonempty coordinate subset has weight sum zero. Follow the proof of fermat_general in PEqualNP/Gct/Helpers/FermatFromKneser.lean. Use the weighted dot form in the annihilator argument, and for each stabilizer-idempotent block use the restricted weights. In the scalar-stabilizer case, 1 belongs to no isotropic W by the subset-sum condition, so Kneser gives dimension of (W+ℂ1)W at least 2 dim W and weighted orthogonality gives 3 dim W at most the number of coordinates. The induction proceeds on the idempotent blocks as in the public proof. Here a subset sum cannot vanish because 9a=125b has no nonzero solution with 0≤a≤25 and 0≤b≤10. This bounds d by 11, short of the requested 8.

On doubly centered matrices, row and column partitions with singleton blocks vanish in M_4 by summing over that singleton index. The only remaining types are [4] with Möbius weight −6 and [2,2] with weight 1. Their combinations give

    M_4 = 36Σ A_ij⁴ −18Σ_i(Σ_j A_ij²)² −18Σ_j(Σ_i A_ij²)²
          +3(Σ A_ij²)² +6 tr((A Aᵀ)²).

Thus the quartic adds non-Fermat contractions. In fact a genuine level line need not have vanishing fourth moment: take A=uvᵀ, u=(1,−1,i,−i,0), v=(1,−1,0,0,0). Then M_k=(k!)² e_k(u)e_k(v). For k=1 and 2, e_k(u)=0. For k≥3, e_k(v)=0. But Σ A_ij⁴=8. This rules out naively applying the iterated Fermat theorem in the same coordinates. As an additional comparison, the direct sum of the two 2×2 checkerboard matrices scaled by 1 and i, plus a 1×1 zero block, has matching coefficients M_1=M_2=M_3=0 and fourth moment 8, with M_4=−96.

## Projection and support restrictions

If every single-row projection has rank at most 2 and dim L≥9, then L contains a nonzero vector supported on each individual row (the four other row projections together have rank ≤8). These five independent block-supported vectors span a subspace that satisfies the stronger all-column-set invisibility condition after transposing. In fact vary independent scalars on the rows, and each coefficient for a distinct row set is a nonzero factorial times the corresponding injective sum. The repository's InvisibleBlock.lemmaI bounds that space by 4, a contradiction. The same reasoning applies with rows and columns exchanged. More generally, the sum of the dimensions of all one-row-supported spaces in L is at most 4.

If the bipartite support graph of L has matching number ≤2, it has a vertex cover of size ≤2 by König. With two covering vertices on one side, the matrices lie in two rows or two columns. The matching quadratic on that 10-dimensional ambient is the product pairing (v,w) ↦ (Σv)(Σw)−v⋅w, which is nondegenerate, and restricting to total zero leaves an isotropic bound 4. With one covering vertex on each side, the support is a row-column cross of dimension 9. The linear coefficient eliminates the corner, and the quadratic is twice the product of the off-corner row sum and the off-corner column sum. Either linear functional must vanish identically on L, bounding its dimension by 7.

## Reproduction

    python /workspace/pnp-session/upper-bound/check_moments.py

The script verifies the quadratic and cubic matching identities in the full 25-variable polynomial ring, the shifted identities on s=0, the quartic identity on an independent 16-variable parametrization of the doubly centered matrices, and the two explicit examples over ℚ(i). Its output is exact symbolic arithmetic.

    OPENBLAS_NUM_THREADS=1 python /workspace/pnp-session/upper-bound/search_rankone.py 5 10000

This heuristic samples linearly independent tensor sets from the 5,920 tensors generated by 89 normalized sparse root-of-unity profiles modulo the prime 1073742361. It uses the permanent rank-one expansion in the public SupportCriterion.lean to reject conflicts. The best observed dimension was 7 after the 10,000 starts. This is a finite modular heuristic for a small basis pool. It does not exhaust that pool's subspaces or the complex search space and gives no universal upper bound.

## Exact coordinate-support restriction

Any counterexample must have at least 19 active entries, and if it has exactly 19 entries the Hessian on its support tangent must be nondegenerate. This is a restriction on the set of coordinates that are nonzero somewhere in L. An arbitrary L can have all 25 active entries.

Let H be the bipartite graph of active entries, m its edge count, B its 10×m unsigned incidence matrix, and d=B1. On the space of vectors supported on H with total zero, the Hessian is the restriction of I−BᵀB. Its radical consists of vectors x of total zero with x−BᵀBx=λ1. Put u=Bx. The radical is isomorphic to the kernel of

    [ I−BBᵀ  −d ]
    [  −dᵀ    −m ].

The isomorphism maps (u,λ) to Bᵀu+λ1. The modular sweep support_sweep.cpp enumerates all 376,992 support patterns up to row permutation, using masks on the five columns and five nondecreasing row masks. Rank over ℤ/1009 lower bounds rank over ℚ and ℂ, so the resulting modular nullity is a valid upper bound on radical dimension. A form on the (m−1)-dimensional tangent with radical dimension n gives an isotropic dimension upper bound floor((m−1+n)/2). This is at most 8 for all patterns of size at most 17. Among the 6,550 patterns of size 18, exactly 140 remain after the Hessian test, all with radical dimension at most 1. At size 19, only the 20 singular-tangent candidates are considered by the next step. There are 2,760 further size-19 candidates with nondegenerate tangent, where the Hessian alone allows 9.

The exact rational script radical_reduce.py considers the 160 singular-tangent candidates at sizes 18 and 19. When the Hessian gives a bound of 9 and a dimension-9 L is sought, L must include the entire radical, since projection to the nondegenerate quotient can have dimension at most the Witt index. For each forced radical vector R, the higher matching polynomials vanish at R, and all their first and second derivatives at R vanish on L along directions from L. Thus restrict the ambient to the joint kernel of first derivatives. A second derivative supplies another form under which L is isotropic, so any linear combination with the original form may give a stronger rank bound. Iterate when the original form acquires a new radical in the restricted ambient. All computations are rational.

At size 18, 40 patterns are ruled out by nonzero cubic on the radical and 80 by a rank bound from higher polarized forms. The 20 remaining patterns form one row/column permutation orbit, represented by row masks [1,15,15,15,31]. The 20 singular size-19 patterns are one orbit, represented by [3,29,29,29,31]. None of the remaining patterns is a candidate counterexample, by the following argument.

In the size-18 representative, separate off column 0 and row 4, whose common entry is the corner. The inner 4×4 matrix of perturbations contains an active 3×3 block A with one zero extra row and column. The first-derivative constraints force the tangent restricted to total sum of A equal to zero. That restricted quadratic form has a two-dimensional radical, generated by R₁ supported on the four non-corner entries of column 0 with values (−3,1,1,1), and R₂ supported on the four non-corner entries of row 4 with values (1,1,1,−3). Thus R₁,R₂∈L. The coefficient of λμ in per(J+X+λR₁+μR₂) is 2S₁(A)+4S₂(A)+9S₃(A) where S_k is the unordered k-matching sum, by a 4×4 cofactor expansion verified symbolically in check_sparse_border.py. Since this vanishes on L, scaling X gives S_k(A)=0 separately.

In the size-19 representative the same inner block contains an additional free entry h in the corner of its otherwise zero extra row and column. Its initial radical is the span of R=R₁+R₂, where R₁ has column values (3,−1,−1,−1) and R₂ row values (−3,1,1,1). Since each permanent term contains at most one R₁ entry and at most one R₂ entry, the coefficient of z² in per(J+X+zR) is the mixed coefficient. It equals −2S₁(A)−18h−4S₂(A)−4hS₁(A)−9S₃(A)−hS₂(A). Scaling X gives h=−S₁(A)/9, and if h=0 then S₂(A)=S₃(A)=0 too.

In either case let K be the kernel of the A projection restricted to L and k=dim K. Since h=0 there, K is supported on the border cross. Its non-corner column entries are a∈ℂ⁴ and non-corner row entries are b∈ℂ⁴, and the corner is −α−β where α=sum a and β=sum b. Its Hessian quadratic is 2αβ, so either α or β vanishes identically on K. Its annihilator in the 8 border coordinates has dimension 8−k and contains a constant direction supported on one of the two four-coordinate sets.

For any X∈L with inner 4×4 block C and border sums α',β', polarization of the Hessian against a member of K gives

    a⋅(β'1 − rowSums(C)) + b⋅(α'1 − colSums(C)) = 0.

To check the formula without assuming total(C)=0, use the corner of X equal to −α'−β'−total(C). The extra total(C) terms from the corner product cancel those from the marginal terms. Projecting each four-coordinate dual vector to its mean-zero part kills the constant direction in the annihilator, so the image of the centered marginals of C on L has rank at most 7−k. These marginals factor through the A projection, since C is determined by A and h. If dim L≥9, their kernel in the A-image has dimension at least (9−k)−(7−k)=2. In size 18 the extra row and column are zero, so centered marginals zero implies actual marginals zero. In size 19 the inner total is S₁(A)+h=−8h and the extra row sum is h. A zero centered marginal at the extra row yields h+2h=0, so h=0 and again actual marginals vanish. Thus the kernel is a doubly centered 3×3 level space of dimension at least 2.

This is impossible. In centered 3×3 Fourier coordinates a,b,c,d using the two nontrivial characters on each axis, the Hessian is a nonzero scalar times ad+bc and the cubic is a nonzero scalar times a³+b³+c³+d³. Indeed a cubic of three such characters can have weight zero mod 3 on each axis only if all three characters coincide. The 2×2 matrix [[a,b],[c,−d]] then has rank at most 1. A 2-dimensional rank-one space has a common row or common column factor. For a common row factor, up to swapping rows its coordinates are c=ka, d=−kb. The cubic is (1+k³)a³+(1−k³)b³, which cannot be zero identically. For a common column factor transpose the argument. This eliminates the two residual support orbits.

Reproduction from the upper-bound directory:

    g++ -O3 -std=c++17 support_sweep.cpp -o support_sweep
    ./support_sweep > support_sweep.log 2> radical_supports.txt
    python radical_reduce.py | tee radical_reduce.log
    python check_sparse_border.py

This finite sweep proves a necessary condition on coordinate supports, coupled with the written proof of the two residual orbits. It is unformalized and does not exhaust spaces with nondegenerate 19-cell support or spaces with 20 to 25 active entries.
