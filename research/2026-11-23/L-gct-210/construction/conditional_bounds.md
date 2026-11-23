# L-gct-210 construction investigation

Let J denote the all-ones 5 by 5 matrix. Let (L) be a complex linear space with the identity (\operatorname{per}(J+t)=120) for (t\in L). For each (t), apply this identity to all scalar multiples of (t). Every nonconstant coefficient of (\operatorname{per}(J+z t)) is zero. Polarization gives the analogous mixed matching sums for directions in (L). These arguments are mathematical scratch work, without Lean formalization.

## Hessian and real directions

The linear coefficient is (24 S), where (S=\sum_{ij} t_{ij}). The second coefficient is (3!) times the sum over size-two matchings, i.e. (3!/2) times (S^2-\sum_i R_i^2-\sum_j C_j^2+\sum_{ij}t_{ij}^2), with row and column sums (R_i,C_j).

On (S=0), write (t=u+r\mathbf1^T+\mathbf1 c^T), where (u) has every row and column sum zero, (\sum r=\sum c=0), and the three parts are orthogonal in the entrywise bilinear dot product. The quadratic form is
$$
\sum_{ij}u_{ij}^2-20(\sum_i r_i^2+\sum_j c_j^2).
$$
In particular, any real admissible direction space projects injectively to the eight-dimensional row/column mean part. A conjugation-invariant complex (L) is the complexification of its real part, so also has dimension at most eight. Over (\mathbb C) without this hypothesis the form has Witt index twelve.

Any complex (L) of dimension at least nine meets the doubly centered subspace nontrivially. Every row or column image of (L) excludes the all-ones vector, since a matrix with a constant nonzero row/column could be scaled to kill that row/column in (J+t). Hence every row or column projection has rank at most four. At the other extreme, the accepted 4-by-5 bound in L-gct-215 implies every row/column projection of a dimension-nine (L) would have rank at least two. Indeed a rank-zero or rank-one projection would leave at least eight dimensions supported in a 4-by-5 slice. The matching-sum coefficients on that slice are the same after padding a zero row.

## Maximality of the known seven-dimensional hook

The hook consists of top row directions with sum zero, and first-column directions below the top with sum zero. All matching coefficients vanish: the only possible mixed quadratic term is a product of the nonleading top row sum and the lower first-column sum, which is zero. The two independent pieces have dimensions four and three.

Suppose (L) contains the hook and consider (t\in L). Quadratic polarization against the top-row directions makes all five column sums of the lower 4-by-5 matrix equal, say (c). Polarization against the first-column directions makes all four row sums of the lower-right 4-by-4 block (B) equal. Comparing total sums makes each equal (c).

The cubic mixed matching coefficient involving (t), top-row direction (x), and first-column direction (y) is, up to a nonzero factorial, (\sum_{i,j>0} y_i x_j (2c+B_{ij})). The only available cells for (t) are in (B) outside row (i) and column (j). The zero-sum restriction on (x) leaves its four coordinates (j>0) arbitrary. The vector (y) ranges over every sum-zero four-vector. Thus every column of (B) is constant, necessarily (c/4).

Subtract hook directions from (t) to arrange a constant top row and a constant lower first column. The resulting lower four rows equal (c/4) in every entry. The top row equals (-c) in every entry by the linear coefficient. If (c\ne 0), scaling this direction kills the entire top row of (J+t), a contradiction. Therefore (t) was in the hook already.

## Conditional bound when a full sum-zero row is present

Assume (L) contains every sum-zero direction supported in its first row. Write (U) for its projection on the lower four rows. For (y\in U) choose a lift (t). Arbitrary first-row sum-zero variation of (J+t), followed by expansion along that row, forces all five lower 4-by-4 permanental cofactors equal. On the line (z t) their common polynomial value (p(z)) obeys
$$
p(z) (5+z\,\sum_j t_{0j})=120.
$$
The product of these complex polynomials is a nonzero constant, so the top row sum vanishes and the cofactors all remain identically (24). The kernel of restriction to the lower rows is exactly the four-dimensional, sum-zero top-row space.

Let (V\subset\mathbb C^4) be the three-dimensional sum-zero hyperplane with its nondegenerate dot product. The degree-one coefficient of each lower cofactor forces the sum over the four included column sums to vanish, which forces each column sum zero. Thus lower column (c_j) gives a linear map (U\to V). Let (s=\sum_j c_j). Degree two gives (\sum_{a<b, a,b\ne j} c_a\cdot c_b=0) for each omitted column (j). Summing over omitted columns gives the total pair sum zero. Subtracting gives (c_j\cdot(s-c_j)=0). With (d_j=2c_j-s), it follows that
$$
d_j\cdot d_j=s\cdot s,qquad \sum_j d_j=-3s.
$$

Let (q) be the pullback of the dot product under (s), and (N) its radical in (U). Polarization identifies (q) with the pullback under every (d_j).

If (\operatorname{rank} q\ge 2), then each image of (d_j) is nondegenerate: a dimension-two subspace of (V) with degenerate restriction has form rank at most one, whereas any dimension-three subspace is all of (V). The same applies to (s). Therefore (N) is the common kernel of (s) and all (d_j), hence is zero because the (c_j) jointly distinguish elements of (U). In this case (\dim U=\operatorname{rank} q\le 3).

If (\operatorname{rank} q\le 1), on (N) each of (s,d_0,\ldots,d_4) takes values on one isotropic line or is zero. Indeed their individual image dot products are zero by polarization, and (V) has Witt index one. Let (m) be the number of nonzero image lines counted with multiplicity among these six maps and (r) the dimension of their span. The relation (\sum_j d_j=-3s) and joint injectivity imply (\dim N\le m-r). Thus (\dim U\ge5) is possible only for (r\le 1), or for (r=2,m=6,\dim N=4,\operatorname{rank}q=1).

If (r\le 1), all columns on (N) are multiples of one fixed isotropic vector (u). If (\dim U\ge5), then (\dim N\ge4) and the scalar coordinate projection on some four of the five columns is surjective. Along those four columns the mixed matching degree (k) is a nonzero factorial multiple of (e_k(u)e_k(\alpha)), where (\alpha) is the vector of four column scalars. Since (u\ne0), (e_1(u)=e_2(u)=0), and (\prod_i(X-u_i)) cannot be (X^4), at least one of (e_3(u),e_4(u)) is nonzero. The corresponding cofactor coefficient cannot vanish for every (\alpha). The case of all zero columns has (N=0).

In the remaining case the nonzero isotropic lines span a two-plane, whose restricted dot product has exactly the two isotropic lines. All maps have nonzero lines. Since (\dim N=m-r=4), the scalar tuples of these six maps cover the entire solution space of the two linear constraints (\sum_j d_j=-3s). Partition the (d_j) into groups according to their lines. Both groups have at least one member: otherwise the relation forces either the single other image line of (s) to be zero or (r=1). On (s=0), the column scalars can be arbitrary with separate sum zero in each group, and each column is (d_j/2).

For group sizes 1 and 4, activate only the four-column group. If its vector has (e_3\ne0), take exactly three nonzero sum-zero scalars and include those columns in a cofactor. If (e_4\ne0), take four nonzero sum-zero scalars and include all four. Either choice gives a nonzero homogeneous coefficient.

For group sizes 2 and 3, write (u) for the size-three line and (v) for the size-two line. Activate only (u), with all three nonzero scalars summing to zero; degree three makes (e_3(u)=0). Together with (e_1(u)=e_2(u)=0), this means (u) is a permutation and scaling of ((1,i,-1,-i)) by its monic root polynomial. Activate the size-two group with scalars ((b,-b)) and omit one of them when forming the cofactor, leaving all three size-three columns. The contribution with two (u) columns and one (v) column to the degree-three coefficient is proportional to (e_2(\alpha_u)b \sum_i u_i^2v_i). To see the last factor, sum (u_a u_b v_c) over distinct row triples, obtaining (2\sum_i u_i^2v_i) because each vector has sum zero. The pure (u) contribution is zero. Allowing (e_2(\alpha_u)b\ne0) forces (u^{\circ 2}\cdot v=0).

The subspace orthogonal to both (\mathbf1) and (u^{\circ 2}) is spanned by (u) and the root vector ((1,-i,-1,i)) in the same coordinate order. Its two isotropic lines are exactly the spans of those vectors. Since (u) and (v) are distinct lines, normalize (v=(1,-i,-1,i)) and (u=(1,i,-1,-i)). Set the size-three group scalars to ((1,-1,0)) and the size-two scalars to ((1,-1)), and omit the zero column. The degree-four cofactor term, up to the product of the four nonzero scalars, is the permanent with columns (u,u,v,v). Inclusion-exclusion over distinct row assignments gives
$$
2(u\cdot v)^2-6\sum_i u_i^2 v_i^2=2\cdot 16-6\cdot 4=8.
$$
The other partitions vanish by zero sums or the two self-dot products. This contradicts the cofactor identity.

Thus (\dim U\le4) and (\dim L\le 8) when the full sum-zero one-row direction space is contained in (L). The transpose gives the corresponding one-column statement. The row-projection restrictions alone do not imply this hypothesis.

## Support must admit a perfect matching

Consider the bipartite graph on five row and five column vertices, with an edge when that coordinate is not identically zero on L. If it has no perfect matching, König's theorem gives a vertex cover of size at most four. Enlarge it to four vertices, split as r rows and c columns. Permuting rows and columns, all directions are supported on their union.

If (r,c) is (4,0) or (0,4), the accepted L-gct-215 applies after padding the missing zero row or column. For mixed covers, use the Hessian on the support's total-sum-zero hyperplane. A vector t lies in the radical exactly when
$$
t_{ij}-R_i-C_j=\lambda
$$
on all supported cells, for some scalar λ, where R and C are its row and column sums. This comes from the annihilator of the one total-sum equation. For a fully included row or column, summing its five cells forces its sum to be −5λ/4. For a partially included row, summing over the c included columns gives (1−c)R_i=−cλ/4, and similarly (1−r)C_j=−rλ/4 for a partially included column.

For (r,c)=(2,2), summing the row sums forces λ=0, hence all row and column sums and then all cells are zero. The tangent dimension is 15 and the radical is zero, so the Witt bound is seven. For (r,c)=(3,1), the partial-row equation forces λ=0 and leaves only the two partial-row sums, with their total zero, free. The tangent dimension is 16 and the radical dimension is one, so the Witt bound is eight. The transpose handles (1,3). Thus any 9-plane must have a perfect matching in its support even though its degree-five permanent vanishes identically.

## One-sided cyclic symmetry

If L is invariant under a 5-cycle of rows, split it into the five eigenspaces of that row permutation. Choose a primitive fifth root of unity ζ and let u_a have entries ζ^(a·i). The part of L in weight a consists of outer products u_a vᵀ for profiles v in some subspace V_a of C⁵. Weight zero has constant rows, so V_0=0 by the zero-row obstruction.

The top coefficient of a weight-a direction is 5! times the product of the entries of u_a and of v. Since every entry of u_a is nonzero, V_a lies in the union of the coordinate hyperplanes. A linear space over C cannot be covered by finitely many proper subspaces, so it lies in a fixed coordinate hyperplane v_i=0.

Opposite nonzero weights a and −a pair under the Hessian as vᵀ(J−I)w times a nonzero row pairing. Thus dim V_a+dim V_−a≤5. Equality would force V_−a to be the full orthogonal complement of V_a for this pairing. But (J−I)⁻¹e_i belongs to that complement and has entries −3/4 at i and 1/4 elsewhere. This contradicts V_−a lying in a coordinate hyperplane. Each opposite pair contributes at most four dimensions, so dim L≤8. The transpose treats invariance under a 5-cycle of columns. No reduction to this symmetry is established.

## Computational checks for tensor and simultaneous-cyclic families

The search scripts fourier_search.py and enriched_tensor_search.py reduce the exact matching-sum coefficient obstruction for tensor-basis subsets to forbidden masks. The key expansion is also in upstream Gct.Helpers.SupportCriterion. Nonzero coefficients modulo the selected prime give sound exclusions of coefficients over the corresponding number fields. The augmented script uses exact recursive subset search. It examined all 1,326 unordered pairs of 51 bases constructed by cycle Fourier, centered trivial modes, signed differences, Helmert normalization, and Witt combinations. It found a 7-dimensional hook basis and ruled out dimension eight or larger in every tested pair. This does not exhaust all possible tensor bases or general subspaces.

For simultaneous 5-cycles on rows and columns, the five weight spaces each have dimensions five. Their top homogeneous restriction is the same circulant permanent polynomial P(z), since the product of the five phases is one. The script circulant.py shows its gradient ideal is the unit ideal on the chart z_0=1 modulo 7. Cyclic symmetry covers all projective charts, and projective reduction gives the same absence of singularities over C. A smooth hypersurface in P⁴ cannot contain P², since the two normal partial derivatives along P² would have a common zero there. Thus each of the four nonzero weights contributes at most two dimensions. For weight zero, circulant_fourier.py computes the matching coefficients in the Fourier coordinates after the linear equation. Their affine solution ideal on c_1=1 is zero-dimensional over Q. Symmetry among nonzero frequencies covers all four projective charts. Therefore a simultaneous-cycle invariant space is bounded by nine. A final argument excluding the 9-dimensional case in this family was not obtained.

## Restrictions on row and column ranks

Let D be the dimension of L, r_i the dimension of its image in row i, and R the sum of r_i. Embedding L in the direct sum of these row images shows that its subspace supported only on row i has dimension at least D + r_i − R. The direct sum of all such subspaces lies inside L. Accepted L-gct-111 bounds its dimension by 4. Thus 5D − 4R ≤ 4, so at D=9 one has R≥11 and at least one r_i≥3. Accepted L-gct-123 transposes the conclusion to columns. Accepted L-gct-114 also rules out any dimension-nine space generated by its individually row-supported and column-supported elements.

Together with the row projection bounds above, a putative 9-plane has each row/column projection rank in {2,3,4}, at least one row and one column projection of rank ≥3, and a full matching in its support graph. It contains neither the full sum-zero supported one-row/one-column space nor a real form under entrywise conjugation. These facts still allow coupled complex spaces.
