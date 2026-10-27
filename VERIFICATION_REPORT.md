# Lean verification of the main results of Persistence Pays

**Completed on 26 October 2026 for the manuscript of 2026-10-25, posted as arXiv:2610.35781v1.** Theorem 1, Theorem 2,
Proposition 2.4, and Proposition 3.1 have checked Lean proofs under the
manuscript's assumptions. The actual probability laws, numerical kernels,
and gradient counter are defined in the project. No essential analytic
estimate or scalar admissibility condition remains as an added hypothesis
of a headline result.

The source manuscript has not been modified.

## Certificates

| Manuscript result | Lean declaration | Source |
|---|---|---|
| Theorem 1: adjusted sampler, TV accuracy and gradient complexity | `PersistencePays.A1.theorem_one` | [TheoremOneVerified.lean](PersistencePays/TheoremOneVerified.lean) |
| Theorem 1: positive step and valid epoch lengths | `PersistencePays.A1.theorem_one_parameter_validity` | [TheoremOneVerified.lean](PersistencePays/TheoremOneVerified.lean) |
| Theorem 2: cold-start entropy bound | `PersistencePays.A1.theorem_two_ennreal` | [TheoremTwoComplete.lean](PersistencePays/TheoremTwoComplete.lean) |
| Theorem 2: finite endpoint entropy | `PersistencePays.A1.theorem_two_finite` | [TheoremTwoComplete.lean](PersistencePays/TheoremTwoComplete.lean) |
| Theorem 2: displayed lower bound on its rate | `PersistencePays.theorem_two_rate_lower` | [TheoremTwoLiteral.lean](PersistencePays/TheoremTwoLiteral.lean) |
| Proposition 2.4: step-dependent Gaussian lower bound | `PersistencePays.GaussianLowerBound.proposition_2_4_explicit_step` | [GaussianLowerBound.lean](PersistencePays/GaussianLowerBound.lean) |
| Proposition 2.4: optimized dimension/condition-number lower bound | `PersistencePays.GaussianLowerBound.proposition_2_4` | [GaussianLowerBound.lean](PersistencePays/GaussianLowerBound.lean) |
| Proposition 2.4: actual implementation and gradient count | `PersistencePays.GaussianLowerBound.proposition_2_4_gradient_cost` | [GaussianGradientLowerBound.lean](PersistencePays/GaussianGradientLowerBound.lean) |
| Proposition 3.1: arbitrary joint law, nonsingular Gaussian reference | `PersistencePays.proposition_3_1_affine_law` | [NoOvershoot.lean](PersistencePays/NoOvershoot.lean) |

Theorem 2's extended-real statement explicitly bounds KL itself. Its
finite-entropy companion rules out any ambiguity involving the convention
for infinity under `ENNReal.toReal`. Its moment maximum has exactly the
manuscript's flight-velocity indexing, as checked in
[STATEMENT_AUDIT.md](STATEMENT_AUDIT.md).

## Theorem 1: actual sampler and full cost

The formal theorem applies to every potential satisfying A1 and A2 in
positive finite dimension, every absolutely continuous probability start
with finite actual L2 density norm, and every accuracy \(0<\varepsilon\le1\).
It covers arbitrary \(m>0\), including \(L_H=0\).

For
\[
\kappa=L/m,\quad \ell_H=L_H/m^{3/2},\quad
D=d+\log(M_2/\varepsilon),\quad
\Lambda=\log(2+\kappa+\ell_H+D),
\]
the verified explicit choices are
\[
h_0=\frac{1}{10^{20}\sqrt\Lambda
\sqrt{\kappa D+\ell_H D^{3/2}}},\qquad
h=h_0/\sqrt m,
\]
\[
E=1+\left\lceil10^7\Lambda/h_0\right\rceil,\qquad
N=\left\lceil\log(2/\varepsilon)/\log4\right\rceil.
\]
The sampler's actual output law has TV distance at most epsilon. Every
realized run, including rejected proposals, uses exactly \(NE+1\) gradient
evaluations, and
\[
NE+1\le10^{30}\Lambda^{3/2}
\left(\sqrt{\kappa D}+\sqrt{\ell_H}D^{3/4}\right)
\log(2/\varepsilon)+1.
\]

These deliberately conservative explicit parameters verify the theorem's
existential universal-constant conclusion. They are a different admissible
construction from the manuscript proof's displayed minimum formula. No
claim of optimized constants is made.

The actual sampler retains the exponential threshold throughout an epoch,
subtracts the signed energy defect on acceptance, leaves it unchanged on
rejection, and uses the correct two independent OU noises. Its finite
random-array implementation is proved to have the iterated epoch-kernel
law. The cache persists across epochs.

The proof's coordinate transformation does not introduce an algorithmic
minimizer or Hessian oracle. The finite speed cutoff is used only by the
auxiliary comparison chain; the actual sampler has no cutoff. This finite
choice also handles \(L_H=0\) without division by zero. The initial warm
law is an assumption of the paper's theorem; this certificate does not
replace it with a cold-start complexity theorem.

The cost is the paper's gradient-oracle count. Potential evaluations,
arithmetic, and generation of randomness are not gradient queries.

## Dependency and statement checks

The complete exported dependency closure is checked by
[AxiomAudit.lean](AxiomAudit.lean). It permits only Lean's ordinary logical
axioms:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

There are no accepted `sorry`, `admit`, `sorryAx`, new proof axioms, or
kernel-check bypasses. Supporting results include the actual Gibbs
invariance, no-overshoot inequality, optimal-transport/corrector estimates,
smooth and general-law free-transport bounds, comparison-chain entropy
and moment estimates, stationary warm-start coupling, exact normalization,
and all scalar parameter tests.

The final successful aggregate run is recorded in
[verification.log](verification.log). Its declaration count includes
supporting definitions and lemmas, not just main theorems.

Independent checks of correspondence to the manuscript are recorded in
[STATEMENT_AUDIT.md](STATEMENT_AUDIT.md) and
[MAIN_PARAMETER_AUDIT.md](MAIN_PARAMETER_AUDIT.md).
The complete intended statement specification is
[THEOREM_MAP.md](THEOREM_MAP.md).

## Source and reproducibility

Source: arXiv:2610.35781v1.

PDF SHA256:
`1c1ae6894e3a61484093b19ee7818d50b1ec26b72a041f1e6ae88bad3dee0053`.

Extracted layout-text SHA256:
`f5281e1aa95b1e6f42fd1dc74eb16869ea847d3d5139884741227da24a6695b4`.

The source hash was rechecked after formalization and remains unchanged.

- Lean 4.34.0-rc2, commit
  `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- mathlib commit
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- lean-stat-learning-theory commit
  `d0f506f0a695018265dccb33bcb05e2f5ca1c876`.

Run `python3 -B verify.py` from this project to rebuild the exported
dependencies and run the axiom audit. The script uses pinned read-only local
dependencies and writes build artifacts only under this project. Its
dependency paths can be overridden with the documented environment
variables. The Lake file pins the same external source revisions.

This certification covers the four main mathematical results and their
checked dependencies. It does not certify the manuscript's prose,
historical novelty, numerical experiments, or floating-point implementations.
Historical intermediate work is preserved in
[PROGRESS_HISTORY.md](PROGRESS_HISTORY.md).
