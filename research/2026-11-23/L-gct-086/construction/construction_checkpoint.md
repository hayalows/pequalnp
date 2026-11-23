# L-gct-086 construction checkpoint

The exact assignment asks for an absolute natural number C bounding the dimension of every complex linear direction space L at the all-ones point of the permanent by C times n. This checkpoint contains results for several structured constructions, with no general proof or superlinear example.

## Primitive block profiles with variable sizes

Partition row and column coordinates into disjoint cyclic blocks. On a block of size k take one profile consisting of the consecutive powers of a primitive kth root of unity. Choose an arbitrary bipartite edge set E between the row blocks and the column blocks and use a separate scalar coefficient per edge for the corresponding outer product. These are independent since their rectangular supports are disjoint.

For any chosen coefficient monomial, the row and column factors in the rank-one expansion of the permanent are obtained by multiplying the linear factors row-by-row and column-by-column. On each row block the product is 1 plus a nonzero scalar times the kth power of the sum of that block's incident variables, and similarly on column blocks. Thus the level condition is exactly the absence of any nonzero nonnegative integer edge multiplicity assignment for which each vertex has incident sum either zero or its block size. This is an integral transportation problem with all-or-none demands, and the coefficient factors are nonzero for every feasible multiplicity.

If a connected component is complete bipartite and its two demand totals are unequal, pad its smaller side by one dummy block so that both totals are N. If there is no nonzero original transport, the two lists are an irreducible pair with no equal proper nonempty subset totals. A matching proper total involving the dummy would give a nonzero matching total in the complements, so this reduces to the same obstruction. Order the demands on each side and take the cyclic prefix boundaries modulo N. Distinct pairs of boundaries must give distinct differences, since a repetition gives two nonempty proper equal cyclic intervals. Their count is therefore at most N. In particular the original complete component has at most N edges. Equal side totals immediately give a feasible full transport in a complete component.

More generally, if E is Ferrers, order its two sides so each row neighborhood is an initial segment of the columns and these segments decrease with the row ordering. Let A_i, B_j be the integer prefix demand sums through row i and column j. Label each existing edge (i,j) by A_i−B_j. A label collision yields i<i′ and j<j′ after interchanging the two edges. The demands in the intervals i+1…i′ and j+1…j′ have equal positive sum. The edge (i′,j′) forces the entire interval rectangle in a Ferrers graph, so it supports an integral transport by greedy interval overlaps. If there is no transport, labels are all distinct, giving |E|≤A+B−1 from the possible integer label range, where A and B are the side totals. This includes many nonuniform demand choices and bounds the corresponding level-space dimension linearly.

There is also an absolute linear bound with arbitrary incidence graph when every edge joins two demands comparable by divisibility. Orient each edge toward its larger endpoint b, and charge it to that endpoint. If b charged neighbors have positive demands a dividing b, some subset of those demands sums to b. To see this, append the demands one at a time and track subset sums S in [0,b]. If appending a fails to enlarge S, its closure under adding a when the result remains at most b forces b into S, since 0 is in S and a divides b. Therefore while b is absent, each appended item strictly grows S, and there can be at most b−1 items. A subset summing to b gives a star transport. Thus the transport-free edge count is bounded by the sum of endpoint capacities A+B. This covers, in particular, all choices of block sizes that are powers of the same prime, at arbitrary incidence density. The divisor list claim is proved in DivisorSubset.lean. Lean exited 0, and its axiom check reports only propext, Classical.choice, and Quot.sound.

No proof of a linear bound on arbitrary E and demands was obtained. A sufficient combinatorial statement would be that every finite nonempty bipartite graph with each degree strictly greater than its own positive demand has a nonzero integral transport. Weighted peeling would then give |E|≤A+B for any transport-free graph. The scripts weighted_blocks.py and dense_variable_search.py test this conjecture on selected small profiles by adding all detected forbidden transportation supports to 0–1 programs. The first reported 150 infeasible profiles with mixed weights. The second reported infeasibility in 59 mixed-weight profiles and 27 uniform profiles, and timed out in 12 uniform profiles. These are numerical ILP solver verdicts for specific inputs and no general conclusion is drawn. Every proposed transportation witness is found by complete enumeration of balanced vertex subsets with integral max-flow, and an ILP output with no admissible witness would have been directly verifiable. None was found.

## Fourier tensor subsets with prime-power rectangular dimensions

Fix one r by s rectangle (zero-padded to an ambient square). Take any subset E of elementary tensors of its two cyclic Fourier bases, choosing a separate parameter for each selected basis tensor.

For an n-coordinate Fourier basis with character frequencies a_1,…,a_k and k≤n, its labelled row-side coefficient is the injection sum over distinct row positions of the product of those characters. Möbius inversion on the equality partitions of the k label positions gives
$$
I_n(a_1,\ldots,a_k)=
\sum_{\pi}
\prod_{B\in\pi}
\left((-1)^{|B|-1}(|B|-1)!
\sum_{j=0}^{n-1}\zeta^{j\sum_{i\in B}a_i}\right).
$$
Thus it vanishes if the full frequency sum is nonzero modulo n. When the sum is zero, it is an integer. A nonzero term for a zero-sum partition into t blocks has unsigned value n^t times the product of the (blocksize−1)! values. Repeated-variable coefficients differ from the labelled value by a nonzero factorial normalization.

Suppose n=p^h is a prime power. The single-block term has strictly smallest p-adic valuation. To see this, merging two blocks of sizes x,y with x+y≤p^h replaces their factorial contribution by a factor
$$
\frac{(x+y-1)!}{(x-1)!(y-1)!}
=x\binom{x+y-1}{x}.
$$
By Kummer, v_p of the binomial is the count of carries adding x and y−1. There are no carries before digit v_p(x), and none out of digit h−1, since the sum is at most p^h−1. Thus the ratio has p-adic valuation at most h−1. Across t−1 merges, the factorial valuation gain is at most (t−1)(h−1), while n^t supplies (t−1)h extra. No cancellation against the single-block term is possible. This proves I_n is nonzero exactly for zero total frequency. The same valuation argument works for all degrees k≤p^h when p^h is any prime-power divisor of n.

If both r and s are prime powers, a common nonconstant coefficient appears exactly when a nonempty sequence of at most min(r,s) selected frequency pairs sums to zero in C_r × C_s, permitting repeats. If there is no such sequence, set S=E∪{0} and add min(r,s) copies of S. Zero has its unique representation by the zero choices. Iterated Scherk's inequality for uniquely represented sums gives
$$
1+\min(r,s)|E|\le |\,\min(r,s)S\,|\le rs.
$$
Thus |E|≤max(r,s)−1. For composite r,s, the same argument gives a linear bound whenever each has a prime-power divisor comparable to min(r,s). The zero-total nonvanishing fails in general beyond that valuation range. For example, I_6(1,5,2,4)=−6·6+6²=0. Both its zero-sum partition terms have equal valuation at every prime dividing 6.

The script composite_fourier_search.py generates the exact finite set of forbidden tensor subsets for a selected small rectangle. It evaluates Fourier polynomials at a primitive root in a prime field chosen so the prime is larger than max(r,s)!, which cannot hide a nonzero balanced injection sum of that magnitude. In the 6 by 10 case the integer constraints ruled out dimension at least eleven, as reported by HiGHS in composite_6x10.log. This is computational evidence for that one rectangle, not an asymptotic result.

## Other boundaries

Spaces containing only row-supported or only column-supported independent generators are already bounded by n−1 in L-gct-111 and L-gct-123. The combination is bounded by 2n−2 in L-gct-114. Those bounds cover Fourier choices with standard coordinate profiles on one side; Scherk gives a second proof in that family.

Tensoring known hook spaces does not automatically preserve the level condition. The mixed tensor summands contain rank-one outer products of two sum-zero vectors of nonzero bilinear self-dot products. Their second matching coefficient is nonzero. Any recursive amplification needs a different gadget or additional cancellations that survive mixed tensor products.

The known linear examples and the above restricted upper bounds do not distinguish between a general linear ceiling and superlinear coupled complex constructions.
