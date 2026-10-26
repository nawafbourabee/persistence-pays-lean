# Persistence Pays: Lean 4 formalization

Companion repository for N. Bou-Rabee, *Persistence Pays: Square-root condition-number dependence for Metropolis-adjusted kinetic Langevin Monte Carlo with a non-reversibly updated accept/reject uniform* (arXiv, 2026).

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

Source: `/Users/nawafbou-rabee/Downloads/main_9.pdf`.
PDF SHA256: `1c1ae6894e3a61484093b19ee7818d50b1ec26b72a041f1e6ae88bad3dee0053`.
The manuscript and the reused external formalization were not modified.
