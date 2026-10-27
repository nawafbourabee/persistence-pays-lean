# Independent statement audit of the paper

Audited source: arXiv:2610.35781v1 (audit performed on the manuscript of 2026-10-25; statement numbers follow the arXiv version).
Scope: Theorem 2, its literal-rate/maximum wrappers, normalized Proposition 6.1,
and the Definition 2.2 sampler/normalization/cost interfaces. This audit checks
statement fidelity; kernel verification and axiom reports are separate evidence.
No manuscript changes were made.

## Theorem 2

No mismatch was found in the displayed coefficients, time indices, or laws.

- `A1.theorem_two` uses the actual unadjusted OBABO kernel, with
  `r = exp(-sqrt(m)*h)` and `sigma = sqrt(1-exp(-2*sqrt(m)*h))`.
  These are exactly the two OU half-step coefficients for friction `2*sqrt(m)`.
- The first numerical step is performed before applying entropy decay. The
  input to the finite-entropy theorem is `K z`, and the endpoint is
  `iterateKernel K (n+1) z`.
- `unadjustedFlightMoment ... (K z) k p` first takes the law of `Z_(k+1)`,
  applies the first OU half-step, and integrates the pth power of the actual
  flight velocity. Thus `k=0,...,n-1` is exactly the manuscript's `V_1,...,V_n`.
  `theoremTwoMomentBound_attained` identifies the finite maximum when `n>0`
  and its summands are nonnegative. The formal bound also allows `n=0`, with
  the empty nonnegative maximum equal to zero; this extends the displayed
  theorem's range and does not alter its `n>=1` case.
- The logarithm `log(1/(2*e*m*h^2*(1-sqrt(m)*h)))` equals the displayed
  `log(kappa/(2*e*hbar^2*(1-sqrt(m)*h)))`, since `hbar^2=L*h^2`.
- The shifted energy and potential are represented by explicitly subtracting
  `U(a.minimizer)`. They therefore agree with `H` and `U-U_*` in the paper.
- Finite moments and finite KL after the first step and throughout subsequent
  iterations are established in the dependencies. The headline uses
  `klDiv.toReal`; an explicit exported finite-KL companion is needed to make
  the non-vacuity of this representation immediately visible to readers of
  the certificate. This issue has now been resolved in `TheoremTwoComplete`:
  `A1.theorem_two_finite` exports endpoint KL finiteness and
  `A1.theorem_two_ennreal` proves the literal extended-real KL bound. Both are
  kernel checked, so the certificate does not rely on interpreting infinity
  through `ENNReal.toReal`.

## Definition 2.2 and gradient cost

`actualPath`, `epochKernel`, and `CachedOBABO.simulate` implement the stated
chain. Each attempt uses two independent Gaussian vectors. Its defect is
computed after the first OU half-step; rejection flips that same intermediate
velocity before the second OU half-step. A fresh independent exponential
threshold is drawn once per epoch. Acceptance subtracts the signed defect;
rejection leaves the threshold unchanged.

The finite noise-block law and the sequential Markov-kernel law are proved
equal. The cached implementation is proved to have this law and to maintain
a valid force cache on both branches. It makes exactly one initialization
gradient query and one query per attempted step, including rejected attempts:
`N*E+1`. Potential evaluations are not counted as gradients. Neither threshold
refreshes nor epoch boundaries introduce additional gradient queries.

## Normalization and Proposition 6.1

The exact coordinate map is `(x,v) -> (sqrt(m)*(x-x_*),v)` with
`U_0(y)=U(x_*+y/sqrt(m))-U_*`. The checked normalization theorems establish
Gibbs pushforward, absolute-continuity transfer, exact L2-warmness and TV
invariance, and pathwise/kernel/simulator conjugacy with `h_0=sqrt(m)*h` and
unchanged OU coefficients. The original algorithm does not evaluate the
minimizer; it occurs only in the proof coordinate change. Gradient counts
are unchanged.

The normalized Proposition 6.1 uses `E=n+1`; hence its entropy-decay duration
is `n*h=(E-1)*h`, while its path/noise/gradient accounting uses all `E` steps.
Its cutoff is an arbitrary finite nonnegative auxiliary cutoff satisfying the
explicit scale condition and condition (d). This generalizes the finite
cutoff used in the paper. When `L_H=0`, the manuscript writes `v_*=infinity`.
That convention is not itself a real-valued formal definition: one instead
chooses any sufficiently large finite cutoff satisfying (d). The scale and
trapezoidal conditions then vanish identically, and the actual sampler is
independent of this proof-only cutoff. The final schedule uses such a finite
cutoff and therefore covers `L_H=0` without division by zero.

The checked local rejection bound `0.0102` is stronger than the paper's
sufficient `0.0125`; together with the checked `0.105` unadjusted TV bound it
implies the required pairwise bound below `1/4`.

## Proposition 3.1

`proposition_3_1` and `proposition_3_1_affine_law` have the full no-moment scope.
Their input is an arbitrary probability measure on phase space, and their
entropy is the actual KL of the shear pushforward relative to its moving
position marginal times the Gaussian reference, exactly as in the paper.
No density, finite moment, smoothness, or finite differential entropy is an
input. Joint absolute continuity is derived from the two finite endpoint KLs.
The exported extended-valued theorem even allows infinite endpoint KLs, where
the inequality is automatic.

A nondegenerate Gaussian is parametrized by an arbitrary translation and an
invertible continuous linear map applied to the standard Gaussian. The density
and pushforward formulations are proved equal. This permits every mean and
every positive-definite covariance (choose an invertible covariance square
root); it is not an isotropic or diagonal restriction. The formal public
interface uses this affine parametrization rather than a separate theorem
quantified over mathlib's `IsGaussian` predicate. A standard-Gaussian corollary
is also checked. No fidelity discrepancy was found.

## Proposition 2.4

`GaussianLowerBound.proposition_2_4_explicit_step` is the first displayed
lower bound with dimension `d=k+1`, and `proposition_2_4` gives the optimized
`sqrt(2)/8 * sqrt(kappa) * d^(1/6)` threshold. The explicit factor
`sqrt(1+hbar^6/64)^k` is the paper's `(1+hbar^6/64)^((d-1)/2)`.
The formal result holds for every positive step size, hence also for the
paper's restricted `0<hbar<2` range.

These are position-TV bounds for the actual scheduled adjusted kernel, from
exactly twice the invariant extended law restricted to the soft-coordinate
halfspace. Its half-mass, probability normalization, and domination by twice
the stationary law are proved. Conditioning only on position leaves the
initial momentum and exponential threshold independent with their stated
laws. The result quantifies over every deterministic Boolean threshold-refresh
schedule: constant true gives fresh acceptance uniforms; refresh at epoch
boundaries gives Definition 2.2, including times inside an epoch. The OU
parameters may be any real `r,sigma` satisfying `r^2+sigma^2=1`, which includes
every positive-friction choice in the manuscript.

`gaussianImplementedLaw_eq` identifies that law with the finite-array cached
implementation. `proposition_2_4_gradient_cost` converts TV accuracy at most
one quarter into the literal query lower bound, including the initialization
query. Unused exponential draws at non-refresh steps have no effect on the
law and incur no gradients. No lower bound for an auxiliary or different
chain is substituted for the paper's chain.
