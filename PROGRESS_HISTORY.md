# Historical progress record

The text below records intermediate states. For the completed verification, see README.md and VERIFICATION_REPORT.md. Earlier unresolved dependencies listed here have since been closed.

# Persistence Pays: Lean verification project

Source: `/Users/nawafbou-rabee/Downloads/main_9.pdf`.

PDF SHA256: `1c1ae6894e3a61484093b19ee7818d50b1ec26b72a041f1e6ae88bad3dee0053`.
Layout-text SHA256: `f5281e1aa95b1e6f42fd1dc74eb16869ea847d3d5139884741227da24a6695b4`.
Its extracted text is identical to main_8.pdf. No manuscript is modified.

## Completion criterion

Theorem 1, Theorem 2, Proposition 2.4, and Proposition 3.1 must be formalized with their actual mathematical meanings, assumptions, and conclusions. Supporting analytic results must also be proved or imported from checked Lean libraries. A theorem assuming the manuscript's essential estimates is only a conditional component, not verification of the main result. Algebraic identities alone are not verification of the sampler's invariant law or mixing bound.

No `sorry`, `admit`, or project-specific proof axioms are allowed in accepted proof files. Dependency audits must exclude `sorryAx` and nonstandard proof axioms. Lean's ordinary logical foundations (`propext`, `Classical.choice`, and `Quot.sound`) are permitted and will be disclosed.

## Current status

IN PROGRESS. Theorem 2 and Propositions 3.1 and 2.4 are now Lean-verified. The unconditional Theorem 2 certificate is `PersistencePays.A1.theorem_two` in `TheoremTwoVerified.lean`. Proposition 3.1 covers every joint probability law and every nonsingular affine Gaussian reference, with no moment or differential-entropy assumptions. Proposition 2.4 covers the actual two-warm Gaussian chain, both acceptance rules and arbitrary deterministic refresh schedules, with both the step-dependent and optimized sqrt(kappa)d^(1/6) lower bounds. Theorem 1 remains unverified; its final parameter, normalization, and mixing/gradient-cost assembly is in progress.

The following supporting results have compiled with only the ordinary three logical axioms listed above:

- Lemma 2.1: exact energy decomposition, the two remainder bounds with constants 1/8 and 1/12, the gradient correction bound, actual C2 gradient/Hessian assumptions, and existence of a minimizer.
- The deterministic threshold correction preserves the Gibbs-exponential measure, including both acceptance branches and the switching boundary. Gaussian OU preservation and Gibbs normalization are proved; the sequential attempted-step and epoch kernels preserve the target under A1.
- The all-acceptance criterion, exact conditional rejection probability, and its independent Gaussian-block expectation formula (Proposition 5.1 components).
- A gradient-oracle implementation with a valid cache agrees with the actual path; its counter is exactly NE+1, including rejected attempts.
- Sharp Pinsker inequality for actual measures, KL data processing and auxiliary-kernel chain rules, and propagation of bounded warmness.
- Lemma 3.2's integral inequality for nonsingular affine Gaussian densities, without moment assumptions, and Lemma 3.3's absolute-continuity conclusion from finite endpoint conditional KL.
- Proposition 3.1: the complete conditional-entropy no-overshoot bound, including actual transported joint laws, marginal densities, all support and absolute-continuity obligations, and infinite endpoint KL cases.
- Lemma 5.4: the actual normalized Gibbs energy tail, with the exact constant 2^(3d/2), derived from A1 without added normalization or moment assumptions.
- The adjusted/unadjusted endpoint TV bound from a shared Gaussian block and the actual epoch-rejection probability.
- Proposition 2.4: the actual diagonal Gaussian target and gradient, actual Verlet energy increments, Gaussian tilted laws and product integrals, half-space mass, stationary accepted-crossing flow, arbitrary refresh schedules, warmness propagation, position-TV separation, and scalar optimization.
- Corollary 3.5, the conditional mean–entropy inequality, conditional KL decompositions, and the exact entropy change under a volume-preserving measurable bijection with integrable energy defect.
- Lemma 5.5: the actual stopped exponential Lyapunov drift, including the normalized OU coefficients, good-flight bound, Gaussian integrations, integrability, and constants 0.076 and 2.04.
- Lemma 5.2: jointly measurable maximal coupling of the actual independent Gaussian noise blocks, with the exact endpoint disagreement probability and both full block marginal laws.
- Proposition 5.3: localized coupling for the actual adjusted epoch kernel, with its exact local supremum, geometric term, stationary exit term, and L2-warm exit term.
- Lemma 5.7: the literal capped comparison map, Borel inverse, volume preservation, energy identity, and growth bound.
- Gaussian OU relative-entropy contraction for arbitrary probability laws, including infinite KL, and its conditional phase-space version for the actual OU kernel. The proof uses checked Gaussian reflection, finite Gaussian sums, entropy tensorization, and the semigroup law.
- Lemma 5.6: all five stopped-path moment/exit conclusions for the literal finite Gaussian block, including prefix independence, the maximum-energy bound with probability 0.01, and the third flight moment with constant 6.6.
- Lemma 4.14: exact starting entropy, finite KL, and an actual bounded density for the literal one-step unadjusted kernel, with all Gaussian/Jacobian/integrability premises discharged from A1.
- Lemma 5.8: both conditional-Gaussian-entropy bounds for actual conditional laws; equation (5.2): exact common-noise comparison and accumulated exit error; Lemma 5.11: both actual comparison-chain moment estimates and the density cap, with the stated constants.
- Brenier existence, actual convex-gradient representation and uniqueness for finite-cost optimal quadratic plans with absolutely continuous source; the potential is finite everywhere for source laws equivalent to Lebesgue measure. Joint weak KL lower semicontinuity and conditional Gaussian KL lower semicontinuity are also proved. The actual density-Jacobian identity for the canonical Brenier map is now checked, using a proximal-map proof of second regularity and the area formula. Its exact log-Jacobian entropy identity is also checked. The dynamic free-transport inequality is now proved in `FreeTransportTheorem.lean`.
- The actual law-dependent transport corrector, its conditional-mean bound, all of Lemma 4.2 and Lemma 4.3, the fixed and conditional Gaussian covariance inequalities in Appendix A, and both parts of Lemma 4.9 are checked. The sharp Talagrand inequality for the actual Gibbs target is now checked, including the extended-valued statement for every probability law. The integrated free-transport corrector estimate is now proved without additional analytic premises.
- The actual stopped finite-epoch rejection inequality in Proposition 6.1 is checked, including prefix consistency. Its numerical 0.0102 conclusion is checked under an explicit small-exit hypothesis; this is a component of Proposition 6.1, not verification of the complete proposition.
- Section 6 actual comparison-chain exit, energy, second/fourth flight moments, cutoff-event tails, and positive capped-defect estimates, with the manuscript constants. These are supporting components, not the complete Proposition 6.1.
- The literal static covariance defect of Appendix A.1, including rough Brenier derivatives, the favorable singular sign, conditional covariance trace identification, and all cutoff integrability. Compact posterior smoothness and its global spatial Lipschitz bound are checked. The actual free-flight mean-flow law, local signed Taylor expansion, and polynomial L² remainder bounds are checked separately; their final smooth-case assembly is now complete.
- The actual-law Theorem 2 is now checked without any extra analytic premise: `GaussianSmoothedFreeTransportBound` is proved from A1. Actual Gaussian posterior/conditional mean/covariance identification, local variational flow construction, and density transport from the continuity PDE are checked. The actual Gaussian-mixture continuity/momentum equations, covariance stress bounds, polynomial joint derivative bounds, and signed finite-time cost expansion are now checked. Their final smooth-case assembly is now complete.
- The actual truncation-plus-Gaussian approximation has weak, second-moment, transport-cost, endpoint corrector, conditional-entropy and integrated-entropy convergence. The general-law free-transport inequality is reduced to the explicit smooth bounded-latent inequality; that premise is now proved in `FreeTransportTheorem.lean`.
- Section 6 actual comparison remainder and cold-start entropy bounds, scalar entropy constant 0.0218 and TV closure 0.105 from that entropy bound. The missing actual entropy input is not assumed verified.
- Finite-entropy and finite-moment propagation through every unadjusted and comparison step; exact conditional-entropy kick identities and the curvature bound of Lemma 4.9(ii).
- Finite moments of every unadjusted finite trajectory; the exact scalar entropy recurrence and Theorem 2 parameter constants (conditional scalar components, not the full theorem); existence of finite-cost quadratic optimal plans, Rockafellar potentials, and a.e. differentiability on convex domains.
- Proposition 2.4's gradient-cost lower bound for the actual cached implementation under arbitrary deterministic refresh schedules; L2-warm transfer of path events; finite Gaussian normalized sums; and a maximal coupling measure construction.

The finite Gaussian-block construction and the sequential kernel construction are explicit, and their multistep law equivalence is proved. The cached implementation over multiple epochs has that same law and uses exactly NE+1 gradient evaluations. The clipped rejection-probability bound of Proposition 5.1 is also proved for the actual A1 potential and finite Gaussian block, without extra moment assumptions. Theorem 2 and its optimal-transport/free-transport dependencies are now fully checked. Gaussian OU entropy contraction, including its conditional phase-space form, is now proved for actual measures. Theorem 1 still requires final parameter/complexity and actual-kernel assembly. The comparison corrector, entropy iteration, and actual Section 6 entropy bound now compile. The last aggregate audit passed for 3,392 declarations; this is not a count of main theorem certificates.

## Reproducibility

Lean: 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
mathlib: commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
The additional Gaussian/entropy library is pinned to SLT commit `d0f506f0a695018265dccb33bcb05e2f5ca1c876` from `https://github.com/YuanheZ/lean-stat-learning-theory.git`. Its theorem `GaussianLSI.gaussian_logSobolev_W12_pi` imports successfully with this runtime and depends only on the three allowed foundational axioms. This static inequality is not itself an OU entropy-contraction proof. The local helper optionally reuses its read-only compiled library via `PERSISTENCE_SLT_REUSE`.
The Lake file pins this exact mathlib commit. A normal installation can build with `lake update`, `lake exe cache get`, and `lake build`.

The local verification script reuses an existing read-only runtime and compiled dependencies; it does not alter the separate project containing those dependencies. It writes build output only beneath this project. Its default dependency location is documented in the script and can be overridden with environment variables.

`python3 -B verify.py` builds the exported modules in dependency order and runs `AxiomAudit.lean`. The audit inspects the dependencies of every exported declaration in the PersistencePays namespace and rejects any axiom outside propext, Classical.choice, and Quot.sound. The number of checked declarations is a coverage aid, not a count of main theorems verified.
