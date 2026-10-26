# Verified local library inventory

Initial inventory: 2026-10-25; subsequent entries record completed project proofs.
The sections below retain the chronological research record: statements that a
dependency was outstanding describe that stage, not the current verification
status. See `THEOREM_MAP.md` and `STATEMENT_AUDIT.md` for current certification
and statement-fidelity evidence. These are implementation findings, not a claim
that absent search hits establish nonexistence of a formalization elsewhere.

## Reusable installation

Read-only external project root:

`/Users/nawafbou-rabee/Desktop/quenched-parallel-mcmc/formalization/coupled_jacobi`

Its executable `.tools/lean-4.34.0-rc2-darwin_aarch64/bin/lean` reports Lean
4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
Its mathlib source and compiled objects are in `.lake/packages/mathlib`, pinned at
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.
The installation was executed successfully without changing that project.

## Checked measure and information-theory foundations

* `Mathlib.InformationTheory.KullbackLeibler.Basic`: actual extended-nonnegative
  relative entropy, Gibbs inequality, finite-entropy characterization including
  absolute continuity and integrability of the log-likelihood ratio.
* `Mathlib.InformationTheory.KullbackLeibler.ChainRule`:
  `InformationTheory.klDiv_compProd_eq_add` and `klDiv_compProd_left`.
* `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`:
  `InformationTheory.klDiv_comp_right_le` for Markov kernels and `klDiv_map_le`
  for measurable maps.
* `Mathlib.Probability.Kernel.Disintegration` contains the Standard Borel
  construction and uniqueness theory; `Kernel.CondDistrib` and
  `Kernel.IonescuTulcea` supply conditional distributions and trajectory laws.
* `Mathlib.Probability.Kernel.Invariance` defines actual invariant measures and
  proves that invariance is preserved under kernel composition.

The first kernel test imported the actual modules and ran `#print axioms` on
`klDiv_compProd_eq_add` and `klDiv_comp_right_le`. Each depends only on
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or custom analytic
axiom was reported.

## External results found in the initial inventory

* `.tools/lean-stat-learning-theory/SLT/GaussianLSI/TensorizedGLSI.lean` proves
  `GaussianLSI.gaussian_logSobolev_W12_pi`. Its premises are Gaussian W12
  integrability, differentiability, continuous coordinate derivatives, and
  integrability of `g² log(g²)`. Its conclusion is
  `Ent(g²) ≤ 2 ∫ |∇g|²` for the standard product Gaussian.
  Its compiled theorem was loaded and its axiom list checked: only
  `propext`, `Classical.choice`, and `Quot.sound`.
  This does not by itself establish OU entropy decay for all finite-entropy laws,
  nor log-Sobolev or Talagrand inequalities for arbitrary strongly convex Gibbs
  measures.
* `.tools/vlasov-meanfield/Vlasov/Vlasov/OT/Wasserstein.lean` supplies a W1
  distance defined using a dual formula and associated estimates. It is not a
  Brenier-map or quadratic-transport library.
* `CoupledJacobi/VerletVolume.lean` contains measurable shear equivalences,
  Verlet bijectivity, and volume preservation. Other local modules provide
  Gaussian likelihood, integration-by-parts, and kernel-coupling constructions.
  These were inspected, but importing them would require explicit dependency
  management and auditing the exact reused statements.

## Important foundations not located by source search

Searching all of this pinned mathlib and the relevant external libraries did not
locate the following results needed for the manuscript's present proofs:

* Brenier existence/uniqueness for quadratic optimal transport and stability of
  optimal maps/plans;
* Talagrand's transport-entropy inequality for strongly convex Gibbs measures;
* the McCann density/Jacobian formula for general Brenier maps;
* Alexandrov second differentiability and matrix-valued distributional Hessians
  in the form used by Appendix A;
* a packaged OU relative-entropy contraction theorem covering arbitrary
  finite-entropy laws (this gap is now closed by the project proof below);
* the needed weak lower semicontinuity theorem for relative entropy.

A packaged Pinsker inequality was also not found. This gap has now been filled
in `PersistencePays/Pinsker.lean`: the sharp event and total-variation inequalities
are proved for the actual mathlib relative entropy. The proof derives an entropy
variational bound from an elementary exponential conjugate inequality and combines
it with mathlib's Hoeffding lemma. The compiled theorem
`PersistencePays.pinsker_probabilityTV` uses only `propext`, `Classical.choice`,
and `Quot.sound`.

These are substantial formalization tasks. Treating them as extra assumptions
would yield conditional results, not verification of the manuscript's main
theorems. The availability of elementary convexity, Gaussian calculus, measure
decomposition, or data processing does not close these dependencies by itself.

## Analytic foundations completed in this project

As of 2026-10-25 the following substantial results have been proved from the pinned
mathlib without importing external analytic axioms:

* `KernelEntropy.lean`: actual KL data processing through an arbitrary chronological
  sequence of invariant Markov kernels, preservation of finite entropy and absolute
  continuity, and equality of KL after attaching the same auxiliary kernel.
* `Pinsker.lean`: sharp `TV ≤ sqrt(KL/2)` for arbitrary probability measures.
* `HeatKernelInequality.lean`, `NonnegativeBridge.lean`,
  `GaussianBridgeAlgebra.lean`, `AffineGaussianBridge.lean`: full Lemma 3.2 for
  arbitrary measurable probability densities, arbitrary nonsingular affine
  Gaussian references, and all interpolation times, with no moment hypotheses.
* `GaussianBridgeLaw.lean`: the explicit Gaussian density is proved equal to the
  pushforward of mathlib's actual `stdGaussian` under the corresponding invertible
  affine map.
* `DensityEntropy.lean`, `DensityComparison.lean`, `BridgeAffinity.lean`: the
  no-moment entropy comparison is proved by integrating **nonnegative** `klFun`
  densities. This avoids subtracting infinite differential entropies.
* `TransportEntropy.lean`, `TransportDensity.lean`, `DensitySupport.lean` (written
  by the algebra subagent): Lemma 3.3, actual Radon--Nikodym representations under
  transport, and essential support inclusion for the reference measures.
* `TransportReferences.lean`, `NoOvershoot.lean`: full Proposition 3.1 for actual
  joint probability laws and relative entropies, including infinite endpoint
  entropy cases. The Gaussian is parametrized by an invertible continuous linear
  map and a mean vector, and its actual Gaussian law is identified above.

`#print axioms PersistencePays.proposition_3_1` reports only `propext`,
`Classical.choice`, and `Quot.sound`. This establishes Section 3's central result;
it does not establish the separate Section 4 transport/entropy foundations or the
paper's final sampler-complexity theorem.

## Section 4 progress: unconditional OU entropy contraction

The following additional results now compile with only `propext`,
`Classical.choice`, and `Quot.sound`:

* `TimeScaledEntropy.lean`: full Corollary 3.5, including its integrated form.
* `ConditionalEntropy.lean`: exact conditional-KL decomposition using actual
  disintegration, and Lemma 4.1(S1), including its conditional-mean square.
* `VolumeEntropy.lean`: the exact entropy-change identity for any measurable
  volume-preserving equivalence and normalized Gibbs reference (Lemma 4.4).
* `GaussianIntegrationByParts.lean`, `MehlerDifferentiation.lean`,
  `MehlerTime.lean`: actual Gaussian integration by parts and time differentiation
  of the OU Mehler average for bounded C1 tests with bounded derivative. These
  are foundations; they do not by themselves prove arbitrary-law contraction.
* `OUEntropyContraction.lean`: the full exact inequality
  `KL(OU_q μ | γ) ≤ q KL(μ | γ)` for every probability law and `0 ≤ q ≤ 1`,
  where `OU_q` actually maps `v` to `sqrt(q) v + sqrt(1-q) ξ` with independent
  standard Gaussian `ξ`. Infinite KL is included.
* `ConditionalOU.lean`: the actual `phaseOUKernel` preserves the position marginal
  and contracts its conditional Gaussian KL by `r²`. This is the entropy part
  of Lemma 4.2, with finite conditional entropy and no moment assumption.

The OU proof **does not assume** a log-Sobolev-to-semigroup theorem, entropy
dissipation, smooth approximation, or weak lower semicontinuity. Instead:

1. `EntropyShearer.lean` derives the leave-one-out entropy inequality from the
   pinned SLT `SubAddEnt.entropy_subadditive` and its entropy decomposition.
2. `GaussianFiniteSum.lean` (root agent) and `GaussianShearer.lean` apply that
   inequality to the actual exchangeable Gaussian ridge density, proving the
   coefficient `(n-1)/n` and all required log-integrability.
3. `GaussianReflection.lean` identifies the adjoint Mehler density with the
   actual output probability law using a measure-preserving joint reflection.
4. `GaussianUpdateSemigroup.lean` proves exact composition of the actual laws
   through characteristic functions; `GaussianChannel.lean` proves monotonicity
   in squared correlation by data processing.
5. `OUEntropyContraction.lean` telescopes adjacent ratios to all positive rational
   coefficients. For a real coefficient, extra OU noise compares it with every
   larger rational coefficient; order density closes the estimate, with no
   passage of probability measures or entropy through a limit.

The only extra library used here is the already pinned read-only SLT project
`d0f506f0a695018265dccb33bcb05e2f5ca1c876`. The imported theorem is static entropy
tensorization, not an unproved OU or transport hypothesis. The complete final
OU theorem's printed axioms contain exactly the standard three axioms above.

The remaining Section 4 barrier is genuinely optimal-transport theoretic:
Brenier existence/uniqueness and stability; Talagrand for strongly convex Gibbs;
Alexandrov's Hessian and its positive singular matrix measure; McCann's density
Jacobian; and the conditional-mean-velocity continuity-equation flow needed by
Appendix A. Generic Prokhorov compactness exists in mathlib and can support a
quadratic optimal-plan existence proof. It does not supply these stronger
results automatically. No main sampler theorem has yet been inferred merely
from these foundations.

## Quadratic transport foundations now constructed

The following files now have actual measure-theoretic conclusions and kernel
checks with exactly the standard three axioms:

* `TransportPlanCompactness.lean`: the set of probability couplings of two
  Polish-space marginals is nonempty, closed, and compact for weak convergence.
* `OptimalPlanExistence.lean`: integral costs are weakly lower semicontinuous
  for continuous nonnegative costs, and an actual minimizing probability plan
  exists. The proof uses bounded continuous clipping, monotone convergence, and
  Prokhorov compactness.
* `QuadraticTransport.lean`: the quadratic cost is an infimum over actual
  probability couplings; an optimal plan exists; finite second moments give
  finite quadratic cost and integrability under every coupling.
* `Rockafellar.lean`: an explicitly constructed finite-path supremum has a convex
  effective domain, is convex on that domain, and contains every pair of a
  cyclically monotone relation in its subgradient.
* `ConvexDifferentiability.lean`: localized Rademacher differentiability and the
  Haar-null boundary of a convex domain imply that this relation is a gradient
  graph over almost every source point.
* `CyclicGraph.lean`: a probability coupling carried by such a relation, with
  absolutely continuous source, equals the pushforward of that source by the
  gradient graph. The gradient is proved measurable and pushes the first
  marginal to the actual second marginal.

This does not yet constitute Brenier's theorem: the optimal-plan support must
still be proved cyclically monotone. No cyclic-monotonicity assumption has been
silently discharged by optimality. That bridge is the next separate task.

The missing support bridge is now closed. `PermutationCompetitor.lean` and
`OptimalPermutation.lean` (dependency subagent) build an actual finite-array
rewiring competitor and prove all permutation cost inequalities on an optimal
plan's support. `CyclicCost.lean` converts those finite squared-cost inequalities
to the finite-list inner-product definition used by Rockafellar.

Consequently `Brenier.lean` now proves genuine gradient representation, uniqueness
of the finite-cost optimal plan, and existence/uniqueness under finite second
moments and source absolute continuity. No Brenier assumption is present.
`FullPotential.lean` additionally proves that the constructed potential has full
effective domain and is globally convex and locally Lipschitz when the source is
equivalent to Haar measure, as required at the start of Appendix A. These theorems'
printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

Brenier-map stability, Talagrand, Alexandrov's second-derivative theorem, the
McCann Jacobian identity, and the continuity-equation flow analysis remain
separate outstanding tasks.

## Entropy semicontinuity now constructed

`EntropyTruncation.lean`, `EntropyDual.lean`, and
`ContinuousEntropyTests.lean` establish the full variational formula for actual
KL divergence over bounded continuous tests. This includes infinite KL and
non-absolutely-continuous laws; it does not assume the variational formula.
`EntropySemicontinuity.lean` then proves joint weak lower semicontinuity of KL
and weak lower semicontinuity of conditional KL with its moving first-marginal
reference. `TransportEntropySemicontinuity.lean` proves weak continuity of the
actual free-transport law and consequently lower semicontinuity and
measurability of its conditional entropy in time. All printed axiom lists are
the standard three axioms.

These close the KL part of Lemma 4.6 and the measurability requirement in the
integrated transport-entropy identities. The differential-entropy part also
requires control of second moments; it is not inferred from weak convergence
alone. Alexandrov/McCann and the transport differentiation needed in Appendix A
remain outstanding.

## Rough convex transport and Jacobian gap now closed

The previously outstanding Brenier regularity and Jacobian steps are now
proved in project sources. `ConvexProximal`, `ConvexGradient`,
`ConvexSecondRegularity`, `ProximalPotential`, `ProximalDerivative`, and
`ConvexHessian` construct the actual proximal map, prove its firm
nonexpansiveness and derivative symmetry, and obtain a positive relative
derivative of the convex gradient on a full-volume set. This suffices for
mathlib's area formula; no Alexandrov or McCann theorem is assumed.
`BrenierInverse` proves the a.e. reverse-map identity and injectivity.
`DensityJacobian`, `McCannJacobian`, and `McCannEntropy` then prove the actual
Radon–Nikodym Jacobian and integrable log-Jacobian entropy identity.
`BrenierHessian` and `BrenierLogDet` expose a measurable positive-definite
derivative field for the canonical Brenier map.

The signed scalar integration-by-parts gap is also closed.
`CompactDifference`, `MonotoneDivergence`, and `ConvexDivergence` prove the
compact nonnegative-test divergence inequality by finite differences and
Fatou, deriving weighted derivative integrability. The dependency agent's
Gibbs cutoff and exact Stein identity complete `Talagrand.lean` from these
results, including the deduction of moments from finite Gibbs KL.

`LocalHessian` proves local integrability of the actual Hessian field.
`MollifiedDerivative` proves that the derivative of a mollified monotone
field dominates the mollification of its a.e. derivative in quadratic form.
`ConvexGradientBound` and `ConvexMollification` give local bounds and compact
pairing convergence for explicit shrinking normalized smooth bumps. These
are kernel checked with only the standard three axioms. The matrix-valued
compact divergence assembly, removal of its cutoffs, and the dynamical
transport differentiation in Lemma 4.5 remain in progress; the full main
theorems are not yet verified.

## Static Appendix A covariance defect now closed

`ConvexMatrixDivergence`, `MatrixCutoff`, `MatrixGlobalIBP`, and
`SignedMatrixDefect` now prove the signed matrix integration-by-parts bound,
including cutoff removal and integrability of the weighted rough Hessian.
`MatrixMomentBounds` derives every ordinary boundary integrability condition
from the density bounds printed in Appendix A and the actual second moments.
`CovarianceTrace` identifies the matrix field with the covariance bilinear
form of the actual disintegration kernel. `StaticCovarianceDefect` combines
these results with the checked log-Jacobian and conditional Gaussian entropy
inequalities. Its `A1.lemma_A_1` is the literal Gibbs-target static statement;
all logarithmic integrability follows from finite Gibbs KL and moments.
Every printed axiom dependency is one of the standard three axioms. No
smoothness of the Brenier map or Hessian-contraction integrability is assumed.
The remaining dynamical Lemma 4.5 work concerns the actual smoothed law's
conditional mean flow, its transport identity, and the finite-time expansion.

The compact Gaussian free-flight analytic bridge is now kernel checked in
`GaussianSingleDensity` through `GaussianMeanUpperRate`: actual Gaussian
regression/conditional moments, positive smooth position density, continuity
and momentum PDEs, material acceleration identity, uniform covariance and
linear stress-divergence bounds, and the exact entropy upper-rate inequality.
`A1.gaussianSmoothed_mean_upper_rate` assumes only A1, a compact continuously
parametrized latent probability law, and positive Gaussian smoothing. It does
not assume the covariance identity, PDE, or an integration-by-parts remainder.
All printed declarations have only propext, Classical.choice, and Quot.sound.

`NormalizationLaws`, `NormalizationSampler`, and `NormalizationKernel` now
verify the actual m-to-1 coordinate change: Gibbs pushforward, absolute
continuity, exact L2-warmness and TV invariance, pathwise carried-threshold
accept/reject decisions, the exact epoch kernels and their iterates, and the
cached finite-array simulator with its unchanged N*E+1 gradient count. The
minimizer is used only in a proof coordinate map, not an additional algorithmic
oracle call. `MainOneLogBounds` and `MainPsiLogBound` supply checked uniform
parameter/logarithm estimates for the final complexity schedule.
