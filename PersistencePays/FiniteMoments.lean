import PersistencePays.Assumptions
import PersistencePays.UnadjustedEpochLaw
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Actual finite moments of every unadjusted finite Gaussian trajectory.
The force-growth bound follows from A1, not from an added Lipschitz premise. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.potential_upper_at_minimizer {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (x : E) : U x-U a.minimizer ≤ L/2*‖x-a.minimizer‖^2 := by
  have hd := potential_descent_bound U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L a.upper a.minimizer x
  rw [a.gradient_minimizer, inner_zero_left, add_zero] at hd
  linarith

theorem A1.gradient_linear_growth {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (x : E) : ‖gradient U x‖ ≤ L*‖x-a.minimizer‖ := by
  have hg := gradient_norm_sq_le_energy U (gradient U) (hessian U)
    a.hasGradientAt a.hasHessianAt a.continuous_hessian L a.L_pos a.upper
    (U a.minimizer) a.minimizer_le x
  have hp := mul_le_mul_of_nonneg_left (a.potential_upper_at_minimizer x)
    (show 0 ≤ 2*L by nlinarith [a.L_pos])
  have hn : 0 ≤ L*‖x-a.minimizer‖ := mul_nonneg a.L_pos.le (norm_nonneg _)
  nlinarith [norm_nonneg (gradient U x)]

section Moments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {p : ℝ≥0∞} {X : Ω → E} {Z : Ω → E × E} {ξ : Ω → E}

theorem A1.gradient_memLp {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hX : MemLp X p μ) : MemLp (fun ω => gradient U (X ω)) p μ := by
  have hc := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous
  exact (hX.sub (memLp_const a.minimizer)).of_le_mul
    (hc.comp_aestronglyMeasurable hX.1)
    (Filter.Eventually.of_forall (fun ω => a.gradient_linear_growth (X ω)))

theorem A1.potential_integrable {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hX : MemLp X 2 μ) : Integrable (fun ω => U (X ω)) μ := by
  have hb := (((hX.sub (memLp_const a.minimizer)).norm.integrable_sq).const_mul (L/2)).add
    (integrable_const |U a.minimizer|)
  apply hb.mono' (a.twice_contDiff.continuous.comp_aestronglyMeasurable hX.1)
  apply Filter.Eventually.of_forall
  intro ω
  change ‖U (X ω)‖ ≤ L/2*‖X ω-a.minimizer‖^2+|U a.minimizer|
  rw [Real.norm_eq_abs]
  have hu := a.potential_upper_at_minimizer (X ω)
  have hl := a.minimizer_le (X ω)
  have hn := mul_nonneg (show 0 ≤ L/2 by nlinarith [a.L_pos]) (sq_nonneg ‖X ω-a.minimizer‖)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (U a.minimizer)],
    by linarith [le_abs_self (U a.minimizer)]⟩

theorem A1.phaseEnergy_integrable {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hZ : MemLp Z 2 μ) :
    Integrable (fun ω => phaseEnergy U (Z ω)) μ := by
  have he : (fun ω => phaseEnergy U (Z ω)) =
      (fun ω => U (Z ω).1+‖(Z ω).2‖^2/2) := by
    funext ω
    exact phaseEnergy_eq_norm U (Z ω)
  rw [he]
  exact (a.potential_integrable hZ.fst).add (hZ.snd.norm.integrable_sq.div_const 2)

theorem A1.kick_memLp {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hZ : MemLp Z p μ) (t : ℝ) :
    MemLp (fun ω => kick (gradient U) t (Z ω)) p μ := by
  apply MemLp.of_fst_snd
  exact ⟨hZ.fst, hZ.snd.sub ((a.gradient_memLp hZ.fst).const_smul t)⟩

theorem drift_memLp (hZ : MemLp Z p μ) (t : ℝ) :
    MemLp (fun ω => drift t (Z ω)) p μ := by
  apply MemLp.of_fst_snd
  exact ⟨hZ.fst.add (hZ.snd.const_smul t), hZ.snd⟩

theorem A1.verlet_memLp {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hZ : MemLp Z p μ) (h : ℝ) :
    MemLp (fun ω => verlet (gradient U) h (Z ω)) p μ :=
  a.kick_memLp (drift_memLp (a.kick_memLp hZ (h/2)) h) (h/2)

theorem ou_memLp (hZ : MemLp Z p μ) (hξ : MemLp ξ p μ) (r σ : ℝ) :
    MemLp (fun ω => OBABOPath.ou r σ (ξ ω) (Z ω)) p μ := by
  apply MemLp.of_fst_snd
  exact ⟨hZ.fst, (hZ.snd.const_smul r).add (hξ.const_smul σ)⟩

theorem A1.unadjustedPath_memLp {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (ξ ξ' : ℕ → Ω → E)
    (hξ : ∀ k, MemLp (ξ k) p μ) (hξ' : ∀ k, MemLp (ξ' k) p μ)
    (z : E × E) (n : ℕ) :
    MemLp (fun ω => OBABOPath.unadjustedPath (gradient U) h r σ
      (fun k => ξ k ω) (fun k => ξ' k ω) z n) p μ := by
  induction n with
  | zero => exact memLp_const z
  | succ n ih =>
    exact ou_memLp (a.verlet_memLp (ou_memLp ih (hξ n) r σ) h) (hξ' n) r σ

end Moments

namespace OBABOPath
theorem firstNoise_memLp (n k : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (firstNoise (E := E) n k) p (gaussianBlock n) := by
  by_cases hk : k<n
  · have he := (IsGaussian.memLp_id (stdGaussian E) p hp).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => stdGaussian E) ⟨k,hk⟩)
    have heq : firstNoise (E := E) n k = fun b => b.1 ⟨k,hk⟩ := by
      funext b
      simp [firstNoise, hk]
    rw [heq]
    exact he.comp_fst (Measure.pi (fun _ : Fin n => stdGaussian E))
  · have heq : firstNoise (E := E) n k = fun _ => 0 := by
      funext b
      simp [firstNoise, hk]
    rw [heq]
    exact memLp_const 0

theorem secondNoise_memLp (n k : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (secondNoise (E := E) n k) p (gaussianBlock n) := by
  by_cases hk : k<n
  · have he := (IsGaussian.memLp_id (stdGaussian E) p hp).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => stdGaussian E) ⟨k,hk⟩)
    have heq : secondNoise (E := E) n k = fun b => b.2 ⟨k,hk⟩ := by
      funext b
      simp [secondNoise, hk]
    rw [heq]
    exact he.comp_snd (Measure.pi (fun _ : Fin n => stdGaussian E))
  · have heq : secondNoise (E := E) n k = fun _ => 0 := by
      funext b
      simp [secondNoise, hk]
    rw [heq]
    exact memLp_const 0

theorem unadjusted_block_finite_moments {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (n : ℕ) (z : E × E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun b => unadjustedEpochEndpoint (gradient U) h r σ n (z,b))
      p (gaussianBlock n) :=
  a.unadjustedPath_memLp h r σ (firstNoise n) (secondNoise n)
    (fun k => firstNoise_memLp n k p hp) (fun k => secondNoise_memLp n k p hp) z n

theorem unadjusted_kernel_finite_moments {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (n : ℕ) (z : E × E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p (unadjustedEpochKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ n z) := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hf : Measurable (fun b : NoiseBlock E n =>
      unadjustedEpochEndpoint (gradient U) h r σ n (z,b)) :=
    (measurable_unadjustedEpochEndpoint (gradient U) hg h r σ n).comp
      (measurable_const.prodMk measurable_id)
  rw [unadjustedEpochKernel_apply]
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hf.aemeasurable).mpr
    (unadjusted_block_finite_moments a h r σ n z p hp)

theorem unadjusted_kernel_energy_integrable {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (h r σ : ℝ) (n : ℕ) (z : E × E) :
    Integrable (phaseEnergy U) (unadjustedEpochKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ n z) :=
  a.phaseEnergy_integrable (unadjusted_kernel_finite_moments a h r σ n z 2 (by norm_num))

end OBABOPath
end PersistencePays

#print axioms PersistencePays.A1.gradient_linear_growth
#print axioms PersistencePays.OBABOPath.unadjusted_block_finite_moments
#print axioms PersistencePays.OBABOPath.unadjusted_kernel_energy_integrable
