# Theorem 1 parameter and complexity audit

This report audits the explicit scalar construction against Theorem 1 of
arXiv:2610.35781v1 (audited on the manuscript of 2026-10-25; the statement is unchanged). It does not itself certify the
separate analytic, invariant-law, or coordinate-conjugacy modules.

## Faithful theorem inputs

The normalized inputs are

- `L = κ = L_original / m ≥ 1`;
- `LH = ℓ_H = LH_original / m^(3/2) ≥ 0`;
- integer dimension `d ≥ 1`;
- a finite warmness bound `M ≥ 1` and `0 < ε ≤ 1`.

The exact theorem specializes `M` to the actual L² density norm `M₂`.
Absolute continuity of the initial law is part of that density interpretation;
finite numerical RN norm alone must not be used to silently discard a singular
part. The measure-level theorem explicitly includes absolute continuity.
The checked warmness lemma establishes `M₂ ≥ 1` for a probability density.
Allowing `ε = 1` slightly extends the paper's stated range `(0,1)`.

The definitions agree with the manuscript:

\[
D=d+\log(M/\varepsilon),\quad
\Lambda=\log(2+\kappa+\ell_H+D),\quad
N=\left\lceil\frac{\log(2/\varepsilon)}{\log4}\right\rceil.
\]

The natural-number ceiling is the ordinary ceiling here because its argument
is positive. The exact radius is

\[
R=3d\log2+2\log(16NM^2/\varepsilon^2),\qquad
Q=1.2R+27d+50.
\]

`MainRadiusBounds.main_radius_bounds` proves `D ≥ 1`, `d ≤ D`,
`0 ≤ R ≤ 16D`, and `Q ≤ 100D`. These are slightly more conservative than the
paper's intermediate `Q ≤ 94D`; the universal-constant conclusion is unchanged.

## Explicit admissible construction

The verified construction is an alternative to the proof's particular
minimum formula; it verifies the existential conclusion of Theorem 1, not
that exact displayed choice with its unspecified constant `C`.

Set

\[
S=\kappa D+\ell_H D^{3/2},\qquad
h_0=\frac1{10^{20}\sqrt\Lambda\sqrt S},\qquad
n=\left\lceil\frac{10^7\Lambda}{h_0}\right\rceil,
\qquad E=n+1.
\]

Here `h₀` is the step in normalized `m=1` coordinates. The physical step and
the dimensionless step used in the manuscript are respectively

\[
h=h_0/\sqrt m,\qquad \bar h=h\sqrt L=h_0\sqrt\kappa.
\]

Thus the physical OU factor is `exp(-sqrt(m)*h) = exp(-h₀)`, and
`√m E h = E h₀`. The number `n` in `NormalizedEpochConditions` is precisely
`E-1`; all logarithms and ceilings in conditions (a)–(d) use this indexing.
The actual chain always has `E = n+1` attempted steps per epoch.

The auxiliary proof cutoff is the finite number

\[
v_* = 10^{38}D^{3/2}\Lambda.
\]

It is **not an algorithm input**. It enters only stopped/comparison-law
estimates. In particular, the actual epoch kernel has no cutoff argument.
No evaluations of the minimizer or Hessian, and no cutoff tests, are added to
the implemented sampler. Translation by the minimizer and subtraction of
its potential value occur only in the proof's coordinate normalization.

## Checked admissibility

`main_step_bounds` proves positivity and the exact identity

\[
h_0^2S\Lambda=10^{-40},
\]

and consequently both

\[
h_0^2\kappa D\Lambda\le10^{-40},\qquad
h_0^2\ell_H D^{3/2}\Lambda\le10^{-40}.
\]

It also proves `h₀ ≤ 10⁻²⁰` and
`0 ≤ log(1/h₀²) ≤ 500Λ`. The integer clock satisfies

\[
10^7\Lambda\le nh_0,
\qquad Eh_0\le10000002\Lambda.
\]

The following modules discharge the actual scalar conditions:

- `MainEpochArithmetic.lean`: ceiling bounds and condition (c), using the
  checked normalized rate lower bound `λ ≥ 1/100`.
- `MainHessianParameters.lean`: condition (b), nonnegative cutoff, and
  `ℓ_H h₀³ v_*/12 ≤ .02h₀`.
- `MainPsiLogBound.lean`: the actual comparison-envelope logarithm satisfies
  `log(Ψ/h₀) ≤ 10¹⁰Λ`.
- `MainParameterConditions.lean`: conditions (a), (d), and their assembly
  with (b), (c), and the exact warm radius.

The final scalar theorem is
`PersistencePays.OBABOPath.main_warm_parameters`. Its hypotheses are only
`κ ≥ 1`, `ℓ_H ≥ 0`, `d ≥ 1`, `M ≥ 1`, `0 < ε ≤ 1`.
There are no residual step-size, clock, logarithm, rejection, or large-constant
hypotheses.

The case `ℓ_H=0` is included directly: `S=κD>0`, and the Hessian/scale
inequalities have zero left side. No positive floor on `ℓ_H`, infinity
convention, or limiting argument is needed. Using a finite proof cutoff in
this case is legitimate and does not modify the chain.

## Complexity and computational accounting

`PersistencePays.OBABOPath.main_gradient_complexity` proves

\[
NE\le10^{30}\Lambda^{3/2}
\left(\sqrt{\kappa D}+\sqrt{\ell_H}D^{3/4}\right)
\log(2/\varepsilon).
\]

This is a literal inequality with a universal constant, including both
natural-number ceilings. The large constant is deliberately conservative;
no claim is made that these proof parameters are practically tuned.
The dependence on condition number, dimension, warmness, accuracy, and
Hessian regularity is exactly the theorem's stated dependence.

The separate checked cached-implementation theorem counts `NE+1` gradient
queries: one initialization and one new endpoint gradient per attempted
step, including rejected attempts. The cached gradient is retained across
epochs, so the count is not `N(E+1)`. The finite independent-noise sampler-law
bridge identifies that implementation with the iterated epoch kernel.
This is a gradient-oracle count, as in the manuscript, not a claim that all
arithmetic, potential-value evaluations, and random-number generation are
free in wall-clock time.

## Verification record and limitation of this report

The following final source checks completed successfully:

- `python3 -B verify.py PersistencePays/MainStepBounds.lean`
- `python3 -B verify.py PersistencePays/MainEpochArithmetic.lean`
- `python3 -B verify.py PersistencePays/MainParameterConditions.lean`
- `python3 -B verify.py PersistencePays/MainGradientComplexity.lean`

The root dependency checks include all supporting radius, Hessian, and
comparison-envelope modules. Printed axioms for the final scalar theorems
are only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` or additional assumed theorem.

The scalar construction and complexity part is complete. Certification of
the entire Theorem 1 additionally uses the separately checked actual-chain
Proposition 6.1, normalization/conjugacy, warmness/TV preservation, and the
cached implementation-law bridge. The final aggregate audit records that
assembly; this report does not substitute for it.

## Final independent read of the assembled Theorem 1

The final statement `PersistencePays.A1.theorem_one` in
`PersistencePays/TheoremOneVerified.lean` has now been independently read,
together with its actual simulation, finite randomness, warmness,
normalization, and cost definitions. This statement-level audit passes.

Its mathematical hypotheses are exactly:

1. `A1 U m L`, including `U ∈ C²`, `0 < m ≤ L`, and the pointwise Hessian
   bounds;
2. `A2 U LH`, the actual Hessian-Lipschitz inequality;
3. positive finite dimension;
4. a probability initial law absolutely continuous with respect to the
   actual phase Gibbs law, with finite literal L² density norm;
5. `0 < ε ≤ 1`.

The type-class hypotheses describe a finite-dimensional real inner-product
space with its Borel measurable structure; Euclidean `ℝᵈ` is included.
There are no assumptions on the minimizer's location/value, entropy,
initial moments, acceptance, contraction, density caps, or admissibility
of parameters. `LH ≥ 0` is derived by
`A2.constant_nonneg_of_dimension`, not imposed as a new assumption.

The output distribution is literally the pushforward of

\[
\nu\otimes\bigotimes_{j<N}\operatorname{epochRandomness}(E)
\]

under the phase component of `CachedOBABO.simulate`, using the original
potential `U` and its actual `gradient U`. Each `epochRandomness(E)` is two
independent arrays of `E` standard Gaussian vectors, together with an
independent `Exp(1)` threshold. The threshold is refreshed once per epoch,
updated by subtraction of the energy error on acceptance, and retained on
rejection. Rejection reverses the velocity after the first OU half-step;
the second OU half-step is still performed. This agrees with Definition 2.2.

The friction agrees exactly with Section 2.2: `γ = 2√m`, giving the
half-step coefficient `exp(-√m h) = exp(-t)` in the formal statement.
The normalization map changes positions by `√m(x-x*)` and leaves velocities
unchanged. Its checked laws preserve both the numerical value of `M₂` and
TV and conjugate the actual finite-epoch chain. The final algorithm does
not evaluate or use that normalization map.

The theorem concludes simultaneously:

- TV error at most `ε` for that actual sampled phase-space output law;
- the pointwise identity `calls = N*E+1` for every realized finite input
  array, including rejected attempts;
- the stated universal-constant complexity bound with the single `+1`
  initialization cost.

The `M`, `D`, `κ`, and `ℓ_H` in the final theorem are exactly the quantities
above, with `M` the finite actual norm converted from `ENNReal` to `Real`.
The auxiliary cutoff and the normalized potential do not occur in the final
run definition. The parameter-validity corollary additionally gives a
strictly positive physical step and positive finite epoch counts.

This confirms fidelity of the assembled Theorem 1 statement and its
definition chain. The root aggregate kernel/axiom audit remains the
machine-verification record for the complete dependency graph.
