import PersistencePays.GaussianIntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiating actual Gaussian averages, with domination justified by
Gaussian first moments. -/
open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Parameter derivative of a Gaussian affine average for a bounded C1 test
with bounded derivative. The coefficient bounds only concern a neighborhood
of the time under consideration. -/
theorem hasDerivAt_gaussian_affine_average
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {A B C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfB : ∀ z, ‖f z‖ ≤ B) (hfA : ∀ z, ‖fderiv ℝ f z‖ ≤ A)
    (α β α' β' : ℝ → ℝ) {t : ℝ} {I : Set ℝ} (hI : I ∈ 𝓝 t)
    (hα : ∀ s ∈ I, HasDerivAt α (α' s) s)
    (hβ : ∀ s ∈ I, HasDerivAt β (β' s) s)
    (hαC : ∀ s ∈ I, ‖α' s‖ ≤ C) (hβC : ∀ s ∈ I, ‖β' s‖ ≤ C)
    (x : E) :
    HasDerivAt (fun s => ∫ y, f (α s • x + β s • y) ∂stdGaussian E)
      (∫ y, fderiv ℝ f (α t • x + β t • y) (α' t • x + β' t • y) ∂stdGaussian E) t := by
  let F : ℝ → E → ℝ := fun s y => f (α s • x + β s • y)
  let D : ℝ → E → ℝ := fun s y =>
    fderiv ℝ f (α s • x + β s • y) (α' s • x + β' s • y)
  have hfc := hf.continuous
  have hdc := hf.continuous_fderiv (by norm_num)
  have hi : Integrable (F t) (stdGaussian E) := by
    apply Integrable.of_bound
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable) B
    exact Filter.Eventually.of_forall (fun y => hfB _)
  have hdi : AEStronglyMeasurable (D t) (stdGaussian E) := by
    exact ((hdc.comp (continuous_const.add (continuous_const.smul continuous_id))).clm_apply
      (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  have hb : Integrable (fun y : E => A*C*(‖x‖+‖y‖)) (stdGaussian E) :=
    ((integrable_const ‖x‖).add IsGaussian.integrable_id.norm).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    (bound := fun y => A*C*(‖x‖+‖y‖)) hI _ hi hdi _ hb _).2
  · exact Filter.Eventually.of_forall (fun s =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
  · apply Filter.Eventually.of_forall
    intro y s hs
    dsimp [D]
    calc
      _ ≤ ‖fderiv ℝ f (α s • x + β s • y)‖ * ‖α' s • x + β' s • y‖ :=
        (fderiv ℝ f _).le_opNorm _
      _ ≤ A * (‖α' s • x‖ + ‖β' s • y‖) := by
        gcongr
        · exact hfA _
        · exact norm_add_le _ _
      _ = A * (‖α' s‖ * ‖x‖ + ‖β' s‖ * ‖y‖) := by simp only [norm_smul]
      _ ≤ A * (C * ‖x‖ + C * ‖y‖) := by gcongr <;> first | exact hαC s hs | exact hβC s hs
      _ = _ := by ring
  · apply Filter.Eventually.of_forall
    intro y s hs
    exact ((hf.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt s
      (((hα s hs).smul_const x).add ((hβ s hs).smul_const y))

end
end PersistencePays
#print axioms PersistencePays.hasDerivAt_gaussian_affine_average
