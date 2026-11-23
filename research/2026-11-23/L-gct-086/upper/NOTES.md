# L-gct-086 upper-bound investigations

The exact target asks for a universal constant (C) with (dim Lle Cn) for every complex level space of (operatorname{per}(J+X)=n!). This note proves a restricted linear bound under row-cycle invariance and records obstacles to generalizing it. No result here closes the desk statement.

## Prime-power row-cycle-invariant level spaces

**Proposition.** Let (n=p^e) be a prime power, including (e=1). If (L) is a complex level space and is invariant under a cyclic shift of all rows, then (dim Lle n-1).

We use the rank-one expansion from the checked [L099](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Gct/L099.lean), and the linear transversal theorem [L171](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Gct/L171.lean). Centering is unnecessary for this proposition.

Let (omega) be a primitive (n)-th root of unity and (u_a(i)=omega^{ai}). Cyclic stability gives a direct sum
[
L=igoplus_{a=0}^{n-1} u_aotimes V_a
]
for column-profile subspaces (V_asubseteqmathbb C^n). Choose a basis (v_{a,ell}) of each (V_a). Write (Z_{a,ell}) for its independent parameters. The rank-one expansion says that the coefficient of any parameter monomial (Z^alpha) in the permanent is the product of its row and column polynomial coefficients, multiplied by a nonzero factorial factor. The row and column polynomials are
[
F_r(Z)=prod_i(1+sum_{a,ell}u_a(i)Z_{a,ell}),qquad
F_c(Z)=prod_j(1+sum_{a,ell}v_{a,ell}(j)Z_{a,ell}).
]

**Row support.** For any monomial of degree (1le kle n), write (a_1,ldots,a_k) for its frequencies including multiplicities. Its coefficient in (F_r) times (prod_{a,ell}alpha_{a,ell}!) is
[
I(a_1,ldots,a_k)=sum_{f:[k]hookrightarrow[n]}omega^{sum_t a_t f(t)}.
]
Summing over row equality partitions by Möbius inversion gives
[
I=sum_{pi} n^{|pi|}prod_{Binpi}(-1)^{|B|-1}(|B|-1)!,
]
where only partitions (pi) with (sum_{tin B}a_t=0mod n) for every block (B) contribute. If total frequency is nonzero, there is no such partition. For weight zero, the one-block term is (pm n(k-1)!). It has strictly smaller (p)-adic valuation than any term with (bge 2) blocks of sizes (s_1,ldots,s_b). In fact
[
v_p((k-1)!)-sum_j v_p((s_j-1)!)le(e-1)(b-1).
]
By Legendre's valuation formula, each nonzero term on the left is the floor difference at (p^r), with (1le r<e), because (k-1<p^e). Given (k-1=sum_j(s_j-1)+(b-1)), the difference equals the floor of ((sum_j((s_j-1)mod p^r)+b-1)/p^r), which is at most (b-1). The extra (n^{b-1}) then gives strictly larger valuation for every multiple-block term. Therefore (I
eq0). This proves exactly weight-zero support, even when labels share frequencies. It also gives a short proof of the Fourier-product support aspect of [Thomas's circulant theorem](https://arxiv.org/abs/math/0301048).

**The product identity.** The level hypothesis and the rank-one expansion now imply that every nonconstant weight-zero monomial in (F_c) has zero coefficient. Projection onto this weight-zero part, by averaging (Z_{a,ell}mapstoomega^{ab} Z_{a,ell}) over shifts (b), says
[
sum_{i=0}^{n-1}prod_{j=0}^{n-1}(1+X_{ij})=nqquad	ext{for every }Xin L.
]
There are (n) row-product terms. This transformation used independent parameters on each Fourier component. It fails for a coupled linear space that is merely mapped to a different level space by the row shift.

**Independent zeros.** Let (d=dim L), and let (r(T)) be the dimension of the span in (L^*) of the coordinate linear functionals on rows in (T). Select any basis of (d) coordinate functionals in (L^*), with (b_i) of them from row (i). Then (r(T)gesum_{iin T}b_i). The values of (r) are invariant under cyclic translation of (T), so summing over all translations yields (nr(T)ge |T|sum_i b_i=|T|d). If (dge n), each row subset has rank at least its cardinality. The linear transversal theorem selects one coordinate functional from each row, with all (n) independent. Prescribe (-1) at each selected coordinate to obtain (Xin L) making every product in the last identity zero. Contradiction. This proves the proposition.

The script verify_fourier_support.py computes exact polynomial coefficients in (mathbb Z[omega]/(Phi_n)) and checks this support rule at orders 2, 3, 4, 5, 7, 8, and 9. As a test of the scope of the identity, at (n=6) it finds missing balanced monomials. This finite output complements the valuation proof. It is not a Lean proof.

## Two general induction obstacles

**Hall rectangles alone are insufficient.** For a level space, the projection to any Hall rectangle (R	imes C), (|R|+|C|=n+1), must exclude the all-ones vector. Otherwise (J-X) has an all-zero rectangle with these sizes and permanent zero. But the doubly centered matrices whose main diagonal is fixed zero satisfy this property for every Hall rectangle: (|R|+|C|>n) implies they contain some common index. Their dimension is at least (n^2-3n+1). Thus these affine obstructions alone cannot force a linear dimension bound.

**No universal small row or column projection.** Take a rectangle with (m) rows and (k) columns, and row profiles from Fourier modes (1,ldots,r) of a cycle of length (m>rk). Let their column profiles vary independently in the centered ((k-1))-dimensional subspace of (mathbb C^k). The resulting space is doubly centered. Its row projections have rank (k-1) and its column projections rank (r). Any nonzero size-(j) matching coefficient would have to have row weight zero modulo (m), but (1le jle k) implies each parameter monomial has weight in ([1,rk]). Thus all positive matching sums vanish. Combining this rectangle and its transpose in disjoint row/column blocks gives genuine doubly centered square level spaces of order (m+k) with every individual row and column projection of rank at least (min(r,k-1)), unbounded as (r,k	oinfty). Disjoint-block matching sums factor by their numbers of edges in each block.

The same argument gives a quantitative obstruction to bounded Taylor orders: on a square board one may tensor the first (lfloor (n-1)/k
floor) Fourier rows with the entire centered column space. All matching sums through degree (k) vanish on dimension ((n-1)lfloor(n-1)/k
floor), which is quadratic for fixed (k). We do not assert vanishing in higher degrees.

## Apolar growth formulation and the higher-order obstruction

The permanent's graded apolar algebra has degree-(k) basis indexed by pairs of (k)-element subsets of rows and columns. Multiplication of basis elements takes their disjoint unions, and is zero if either pair of subsets overlaps. It is the equal-bidegree part of the tensor product of two commutative squarefree algebras. Put (s=(sum_i x_i)(sum_j y_j)), and identify the permanent directions (L) with a subspace in degree one. The level condition gives the top-degree identity (L(L+mathbb C s)^{n-1}=0). The complementary nondegenerate pairing of degrees 1 and (n-1) thus gives
[
dim L+dim operatorname{span}[L(L+mathbb C s)^{n-2}]le n^2.
]
The second term is the gradient-span approach in the checked [L083](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Gct/L083.lean). The spaces
[
s^{n-1-k}operatorname{span}[L(L+mathbb C s)^{k-1}]
]
are nested for (1le kle n-1). A lower growth bound on enough stages would yield a linear bound, but none is established here. Strong Lefschetz for multiplication by (s) can control the first stage, rather than successive new directions. In particular, the fourth matching coefficient has rectangle contractions (mathrm{tr}((XX^	op)^2)) even after doubly centering. This prevents direct iteration of a coordinatewise Kneser product argument based on the quadratic and cubic terms.

A leading characteristic-(p) reduction also does not provide a bound by itself. At prime order (p), in Fourier variables, divide each unordered-matching polynomial by (p) and use the same Möbius one-block term. Reduction modulo (p) detects the weight-zero coefficient of a product (prod_j(1+w_j)) in (R=mathbb F_p[s]/(s^p-1)=mathbb F_p[epsilon]/(epsilon^p)), with (epsilon=s-1). All (w_j) may instead lie in (U=epsilon^{lceil p/2
ceil}Rcapker(mathrm{coeff}_{s^0})), and obey (sum_j w_j=0). Then every product of at least two (w_j)'s vanishes, while (dim{(w_j)in U^p:sum_jw_j=0}=(p-1)(lfloor p/2
floor-1)). Thus the leading special fibre has spurious quadratic-dimensional solutions. Any arithmetic route needs additional conditions preventing their lift.

## Root-block models and weighted flow

Partition row positions into blocks with positive sizes (a_i), and column positions into blocks of sizes (b_j). Put one full-root profile (entries running through all roots of unity of the block size) on each block and give each allowed bipartite edge (ij) an independent coefficient (Z_{ij}) on the tensor product of those profiles. By the rank-one support formula, an edge-variable monomial occurs in the row product iff the exponent sums at every row vertex are either zero or exactly (a_i). The corresponding criterion for the column product uses (b_j). The coefficients in these cases are nonzero and the monomial conditions suffice. Thus the matrices form a level space iff there is no nonempty nonnegative integer flow on the allowed edges with each vertex's total either zero or equal to its prescribed weight. The level-space dimension then equals the number of allowed edges, since their matrix supports are pairwise disjoint.

For complete bipartite support the number of edges is less than (n). If the row weights have total (P) at least the column total, the differences of the (r) row partial sums preceding the final row and the (c+1) column partial sums are distinct modulo (P). A collision yields equal sums on nonempty intervals, possibly replacing the row interval by its complement for wraparound. Such equal sums furnish an allowed saturated flow in the complete support, contradiction. Hence (r(c+1)le Ple n), and the number (rc) of edges is less than (n). If the column total is greater, transpose.

For uniform row weights (a) and uniform column weights (b), normalize by (g=gcd(a,b)). An interval transport tree with (b/g) rows of capacity (a/g) and (a/g) columns of capacity (b/g) is obtained by overlaying two partitions of an interval of length (ab/g^2); connect pairs that overlap on a positive length. Because normalized capacities are coprime there is no common internal boundary, so this is a connected acyclic graph and overlaps give integral flow. Any subgraph of minimum row degree at least (a/g), minimum column degree at least (b/g), contains this tree by greedy embedding: at each step fewer than the total number of opposite-side tree vertices have been used. Therefore peeling lower-degree vertices bounds the number of edges in a no-flow graph by
[
(a/g-1)|R|+(b/g-1)|C|.
]
For varying weights this can be applied separately to pairs of weight classes. There are at most (sqrt{2n}) distinct positive weights on either side, producing an (O(n^{3/2})) bound on this particular construction family. It is not the sought linear estimate.

One candidate to sharpen it is the weighted core statement: every finite bipartite graph in which vertex weight is at most its degree has a nonempty saturated flow. If proved, the same peeling argument would give (<2n) for every root-block model. The statement survived the exact search of 71,700 eligible 4×4 configurations up to row permutation and the seeded random search of 31,403 eligible configurations of side sizes up to 12. This is computational evidence only. Searches use the exact weighted Hall criterion on all subsets with equal total weight and skip adjacent equal weights, which give a one-edge saturated flow.

Reproduce:
```
python verify_fourier_support.py
python weighted_balance.py --exact 4 4
python weighted_balance.py --trials 50000 --max-side 12 --seed 2086
```
