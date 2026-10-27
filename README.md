# Persistence Pays: Lean 4 formalization

Companion repository for N. Bou-Rabee, *Persistence Pays: Square-root condition-number dependence for Metropolis-adjusted kinetic Langevin Monte Carlo with a non-reversibly updated accept/reject uniform* (arXiv:2610.35781, 2026).

## The result

The paper proves that Metropolis-adjusted OBABO, run with Neal's non-reversibly updated accept/reject uniform, reaches total variation accuracy epsilon after O~(sqrt(kappa d) + sqrt(L_H) (d/m)^{3/4}) gradient evaluations from a Gaussian start at an approximate minimizer, for targets exp(-U) with m I <= Hessian(U) <= L I and an L_H-Lipschitz Hessian, kappa = L/m. The sqrt(kappa) term is sharp: a Gaussian lower bound (Proposition 2.4) shows that no choice of step size, friction or epoch length removes it. The dimension dependence is not sharp: the upper bound is d^{1/2}, the lower bound d^{1/6}. On Bayesian logistic regression posteriors the measured cost grows like the square root of the condition number at the mode, faster than the theorem's L_H term predicts on that family.

## Key ideas

**Discretizing Lu's entropic hypocoercivity (Theorem 2).** Lu proved that kinetic Langevin dynamics with friction 2 sqrt(m) contracts relative entropy at rate sqrt(m), independently of kappa, using the functional Ent + eta C with C a transport corrector built from the Brenier map. Every step of that argument has an exact counterpart for the OBABO splitting except one: the kicks act at the two ends of a free flight while transport acts throughout, and the discrepancy is exactly the trapezoidal-rule error of the position entropy along the flight. An entropy inequality for free transport (Proposition 3.1), proved from strong subadditivity of entropy along a Brownian bridge, bounds that error. The result is a relative entropy contraction for unadjusted OBABO at rate sqrt(m) in physical time, uniformly in kappa, up to a discretization error that depends on moments of the chain. This part uses nothing about the accept/reject rule.

**Telescoping energy errors (Proposition 5.1).** The energy error of a velocity Verlet step is G(x_1) - G(x_0) + tau, with G = h^2 |grad U|^2 / 8 a function of position only and tau a cubic remainder. Along a path the G terms telescope. With Neal's update, write the uniform drawn at the start of an epoch as u = exp(-ell), so that ell is a standard exponential variable; each accepted move replaces ell by ell - Delta H, and a move is accepted when ell > Delta H. Every move of an epoch of sqrt(kappa)/hbar steps is therefore accepted exactly when the running maximum of the accumulated energy error stays below the single value of ell drawn at the start. The rejection probability of an epoch is then governed by the maximal energy along the path plus the accumulated tau, with no factor of the number of steps. A fresh uniform at every step pays the sum of the positive parts instead. This is what the title refers to, and it is what makes the sqrt(kappa) epoch length affordable.

A coupling argument (Proposition 5.3) combines the two: two copies of the adjusted chain, one stationary, are driven within each epoch by a maximal coupling of the unadjusted chains; on the event that neither rejects, they coincide with the unadjusted chains and meet with the probability Theorem 2 controls.

## What is open

Three gaps are stated in Section 8 of the paper. The dimension dependence: the upper bound is d^{1/2} and the Gaussian lower bound d^{1/6}; the upper bound controls the leading energy error G uniformly over an energy sublevel set of level of order d, and the proximal methods of Chen, Chewi, Lu and Zhang and of Yuan, Guo and Chen reach d^{1/4} on the full class. The Hessian-Lipschitz assumption: the present argument needs it through the cubic bound on tau, and whether the chain itself needs it for square-root acceleration is open. Cold starts: the theorem covers initial laws with finite L^2(mu) norm relative to mu. An accelerated bound from an arbitrary point, without the optimization stage of Remark 2.5, is not expected to hold: the attracting cycles behind the non-acceleration of unadjusted Strang splittings (Bou-Rabee, arXiv:2608.25279) are the obstacle, though no such result is proved for the adjusted chain.

## This repository

**Numbering.** The reports in this repository (THEOREM_MAP.md, STATEMENT_AUDIT.md, VERIFICATION_REPORT.md) refer to the manuscript version `main_9.pdf`, the version the formalization was built from. The arXiv version renumbers some lemmas in Sections 4 and 5 (in particular, Lemma 4.5 of `main_9` was merged into the proof of what is now Lemma 4.7 and Appendix A). The four headline statements, Theorem 1, Theorem 2, Proposition 2.4 and Proposition 3.1, are unchanged.

**License.** Apache License 2.0 (see LICENSE), the license of Mathlib.

---

Theorem 1, Theorem 2, Proposition 2.4, and Proposition 3.1 of `main_9.pdf` are Lean-verified under the manuscript's assumptions, including the actual sampler laws and all gradient costs.

**Start with [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md).** It lists the certificates, exact scope, proof parameters, source hash, and reproducibility information.

## Main certificates

- [TheoremOneVerified.lean](PersistencePays/TheoremOneVerified.lean): `A1.theorem_one` proves actual adjusted-sampler TV accuracy and the complete gradient bound. `A1.theorem_one_parameter_validity` verifies positive step size and valid epochs.
- [TheoremTwoComplete.lean](PersistencePays/TheoremTwoComplete.lean): `A1.theorem_two_ennreal` proves the cold-start entropy bound; `A1.theorem_two_finite` exports finite KL explicitly.
- [GaussianLowerBound.lean](PersistencePays/GaussianLowerBound.lean) and [GaussianGradientLowerBound.lean](PersistencePays/GaussianGradientLowerBound.lean): Proposition 2.4 for both acceptance rules, arbitrary threshold-refresh schedules, and the actual cached implementation.
- [NoOvershoot.lean](PersistencePays/NoOvershoot.lean): Proposition 3.1 for arbitrary joint laws and every nonsingular affine Gaussian reference, with no moment or differential-entropy assumptions.

Theorem 1 uses explicit conservative parameters with universal constant C0=10^30, preserving all the manuscript's complexity exponents. This verifies its existential conclusion with an alternative admissible parameter choice. The proof includes LH=0 and exact NE+1 gradient accounting.

## Verification

The final aggregate build and recursive axiom audit passed for **3,541 exported project declarations**. This includes supporting definitions and lemmas, not just the four main results. No `sorry`, `admit`, `sorryAx`, new proof axioms, or kernel-check bypasses are used. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` occur.

Run `python3 -B verify.py` here to rebuild exported dependencies and run [AxiomAudit.lean](AxiomAudit.lean). See [verification.log](verification.log) for the successful final run. Local read-only dependency locations can be overridden with `PERSISTENCE_LEAN_REUSE`, `PERSISTENCE_LEAN_BIN`, and `PERSISTENCE_SLT_REUSE`.

The [Lake configuration](lakefile.toml) and [toolchain file](lean-toolchain) pin the corresponding source versions. With those dependencies installed, `lake build` builds the library; `lake env lean AxiomAudit.lean` runs the recursive audit.

## Statement fidelity and records

- [THEOREM_MAP.md](THEOREM_MAP.md): intended statements and dependency map.
- [STATEMENT_AUDIT.md](STATEMENT_AUDIT.md): independent manuscript-to-Lean correspondence check.
- [MAIN_PARAMETER_AUDIT.md](MAIN_PARAMETER_AUDIT.md): parameter construction, normalization, and exact complexity audit.
- [PROGRESS_HISTORY.md](PROGRESS_HISTORY.md): preserved intermediate progress, including dependencies that were unresolved at earlier stages.

Source: manuscript version `main_9.pdf`.
PDF SHA256: `1c1ae6894e3a61484093b19ee7818d50b1ec26b72a041f1e6ae88bad3dee0053`.
The manuscript and the reused external formalization were not modified.
