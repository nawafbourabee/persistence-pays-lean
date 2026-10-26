import PersistencePays.ExitCondition

/-! All prefix exit probabilities are controlled by the one actual epoch exit. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stopped_prefix_exit_le {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (h r σ vstar : ℝ) {k n : ℕ} (hk : k ≤ n) (z : E×E) :
    gaussianBlock k (stoppedBlockEvent U (gradient U) h r σ vstar k z)ᶜ ≤
      gaussianBlock n (stoppedBlockEvent U (gradient U) h r σ vstar n z)ᶜ := by
  rw [← (prefixBlock_preserving (E:=E) hk).map_eq,
    Measure.map_apply (prefixBlock_preserving hk).measurable
      (stoppedBlockEvent_measurable a h r σ vstar k z).compl]
  apply measure_mono
  intro b hb hfull
  exact hb (stoppedBlockEvent_prefix U (gradient U) h r σ vstar hk z hfull)

theorem small_exit_sqrt {p h Ψ : ℝ} (hp : 0 ≤ p) (hh : 0 < h) (hΨ : h ≤ Ψ)
    (hb : p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4) :
    Real.sqrt p ≤ (10:ℝ)^(-10:ℤ)*(h/Ψ)^2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · calc
      p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := hb
      _ = ((10:ℝ)^(-10:ℤ)*(h/Ψ)^2)^2 := by norm_num; ring

theorem small_exit_weighted_sqrt {p h Ψ Ξ : ℝ}
    (hp : 0 ≤ p) (hh : 0 < h) (hΨ : 1 ≤ Ψ) (hΞ : 0 ≤ Ξ) (hΞΨ : Ξ ≤ Ψ)
    (hb : p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4) :
    Ξ*Real.sqrt p ≤ (10:ℝ)^(-10:ℤ)*h^2 := by
  have hΨpos : 0 < Ψ := by linarith
  have hs : Real.sqrt p ≤ (10:ℝ)^(-10:ℤ)*(h/Ψ)^2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · calc
        p ≤ (10:ℝ)^(-20:ℤ)*(h/Ψ)^4 := hb
        _ = ((10:ℝ)^(-10:ℤ)*(h/Ψ)^2)^2 := by norm_num; ring
  calc
    _ ≤ Ψ*((10:ℝ)^(-10:ℤ)*(h/Ψ)^2) := mul_le_mul hΞΨ hs (Real.sqrt_nonneg _) hΨpos.le
    _ = ((10:ℝ)^(-10:ℤ)*h^2)/Ψ := by field_simp
    _ ≤ _ := div_le_self (by positivity) hΨ

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.stopped_prefix_exit_le
