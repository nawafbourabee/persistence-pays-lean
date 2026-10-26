import SLT.GaussianLSI.SubAddEnt.Subadditivity
import SLT.GaussianLSI.SubAddEnt.Decomposition

/-! A measure-level entropy Shearer inequality. All marginal entropy
integrability is derived, rather than assumed. The external static
tensorization theorem is from the pinned lean-stat-learning-theory project. -/
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators
namespace PersistencePays
noncomputable section
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]

/-- The sum of the entropies after averaging out one coordinate is at most
`n-1` times the full entropy. No differentiability is required. -/
theorem entropy_leave_one_out (f : (Fin n → Ω) → ℝ)
    (hf : Measurable f) (hn : 0 ≤ᵐ[Measure.pi μs] f)
    (hi : Integrable f (Measure.pi μs))
    (hl : Integrable (fun x => f x * log (f x)) (Measure.pi μs)) :
    (∑ i : Fin n, LogSobolev.entropy (Measure.pi μs)
      (condExpExceptCoord (μs := μs) i f)) ≤
      ((n : ℝ)-1) * LogSobolev.entropy (Measure.pi μs) f := by
  have hsub := SubAddEnt.entropy_subadditive (μs := μs) f hf hn hi hl
  have hdec (i : Fin n) := SubAddEnt.integral_condEntExceptCoord_eq_entropy_sub
    (μs := μs) i f hi hl
    (SubAddEnt.condExpExceptCoord_mul_log_integrable (μs := μs) i f hf hn hi hl)
  simp_rw [hdec] at hsub
  rw [Finset.sum_sub_distrib] at hsub
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsub
  linarith

/-- When all leave-one-out marginals have the same entropy, their common
value contracts by exactly `(n-1)/n`. -/
theorem entropy_symmetric_leave_one_out (f : (Fin n → Ω) → ℝ)
    (hf : Measurable f) (hn : 0 ≤ᵐ[Measure.pi μs] f)
    (hi : Integrable f (Measure.pi μs))
    (hl : Integrable (fun x => f x * log (f x)) (Measure.pi μs))
    {a : ℝ} (ha : ∀ i : Fin n,
      LogSobolev.entropy (Measure.pi μs) (condExpExceptCoord (μs := μs) i f) = a)
    (hnpos : 0 < n) :
    a ≤ (((n : ℝ)-1)/(n : ℝ)) * LogSobolev.entropy (Measure.pi μs) f := by
  have hh := entropy_leave_one_out f hf hn hi hl
  simp_rw [ha] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnreal).2
  nlinarith

end
end PersistencePays
#print axioms PersistencePays.entropy_leave_one_out
#print axioms PersistencePays.entropy_symmetric_leave_one_out
