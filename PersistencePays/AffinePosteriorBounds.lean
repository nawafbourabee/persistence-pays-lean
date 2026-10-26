import PersistencePays.AffinePosteriorDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! Global spatial Lipschitz bounds for compact affine exponential families.
The posterior normalization may be arbitrarily small; it cancels exactly. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped InnerProductSpace NNReal
variable {E Z V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compact_weighted_integral_norm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure Z) [IsFiniteMeasure μ] (w : Z → ℝ) (F : Z → V)
    (hw : Continuous w) (hF : Continuous F) (hw0 : ∀ z, 0≤w z)
    {A : ℝ} (hA : ∀ z, ‖F z‖≤A) :
    ‖∫ z, w z • F z ∂μ‖≤(∫ z, w z ∂μ)*A := by
  have hi := (hw.smul hF).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=μ)
  have hj : Integrable (fun z => w z*A) μ := (hw.mul continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ:=μ)
  calc
    _ ≤ ∫ z, ‖w z • F z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, w z*A ∂μ := integral_mono hi.norm hj (fun z => by
      rw [norm_smul,Real.norm_of_nonneg (hw0 z)]
      exact mul_le_mul_of_nonneg_left (hA z) (hw0 z))
    _ = _ := integral_mul_const A w

theorem affinePosteriorMean_norm (μ : Measure Z) [IsProbabilityMeasure μ]
    (F : Z → V) (H : Z → E) (k : Z → ℝ) (hF : Continuous F) (hH : Continuous H) (hk : Continuous k)
    {A : ℝ} (hA : ∀ z, ‖F z‖≤A) (y : E) : ‖affinePosteriorMean μ F H k y‖≤A := by
  have hw : Continuous (affinePosteriorWeight H k y) := (affinePosteriorWeight_continuous H k hH hk).comp
    (continuous_const.prodMk continuous_id)
  have hp := affinePosterior_normalizer_pos μ H k hH hk y
  have hn := compact_weighted_integral_norm μ _ F hw hF
    (fun z => (Real.exp_pos _).le) hA
  unfold affinePosteriorMean
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  calc
    _ ≤ (∫ z, affinePosteriorWeight H k y z ∂μ)⁻¹*
        ((∫ z, affinePosteriorWeight H k y z ∂μ)*A) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    _ = A := by field_simp

theorem affinePosteriorMean_fderiv_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (F : Z → V) (H : Z → E) (k : Z → ℝ) (hF : Continuous F) (hH : Continuous H) (hk : Continuous k)
    {A B : ℝ} (hA0 : 0≤A) (hB0 : 0≤B)
    (hA : ∀ z, ‖F z‖≤A) (hB : ∀ z, ‖H z‖≤B) (y : E) :
    ‖fderiv ℝ (affinePosteriorMean μ F H k) y‖≤2*A*B := by
  let w := affinePosteriorWeight H k y
  let D := ∫ z, w z ∂μ
  let N := ∫ z, w z • F z ∂μ
  let D' := ∫ z, w z • innerSL ℝ (H z) ∂μ
  let N' := ∫ z, w z • (innerSL ℝ (H z)).smulRight (F z) ∂μ
  have hw : Continuous w := (affinePosteriorWeight_continuous H k hH hk).comp
    (continuous_const.prodMk continuous_id)
  have hw0 (z:Z) : 0≤w z := (Real.exp_pos _).le
  have hp : 0<D := affinePosterior_normalizer_pos μ H k hH hk y
  have hi : Continuous (fun z => innerSL ℝ (H z)) := (innerSL ℝ).continuous.comp hH
  have hij : Continuous (fun z => (innerSL ℝ (H z)).smulRight (F z)) :=
    (ContinuousLinearMap.smulRightL ℝ E V).continuous₂.comp₂ hi hF
  have hN : ‖N‖≤D*A := compact_weighted_integral_norm μ w F hw hF hw0 hA
  have hD' : ‖D'‖≤D*B := compact_weighted_integral_norm μ w _ hw hi hw0
    (fun z => by simpa only [innerSL_apply_norm] using hB z)
  have hN' : ‖N'‖≤D*(B*A) := compact_weighted_integral_norm μ w _ hw hij hw0
    (fun z => by
      rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm]
      exact mul_le_mul (hB z) (hA z) (norm_nonneg _) hB0)
  have hd := (affinePosteriorMean_hasFDerivAt μ F H k hF hH hk y).fderiv
  change fderiv ℝ (affinePosteriorMean μ F H k) y = D⁻¹•N'-(D⁻¹)^2•D'.smulRight N at hd
  rw [hd]
  calc
    _ ≤ ‖D⁻¹•N'‖+‖(D⁻¹)^2•D'.smulRight N‖ := norm_sub_le _ _
    _ = D⁻¹*‖N'‖+(D⁻¹)^2*(‖D'‖*‖N‖) := by
      rw [norm_smul,norm_smul,ContinuousLinearMap.norm_smulRight_apply,
        Real.norm_of_nonneg (inv_nonneg.mpr hp.le),Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ D⁻¹*(D*(B*A))+(D⁻¹)^2*((D*B)*(D*A)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hN' (inv_nonneg.mpr hp.le))
        (mul_le_mul_of_nonneg_left (mul_le_mul hD' hN (norm_nonneg _) (by positivity))
          (sq_nonneg _))
    _ = 2*A*B := by field_simp; ring

theorem affinePosteriorMean_lipschitz (μ : Measure Z) [IsProbabilityMeasure μ]
    (F : Z → V) (H : Z → E) (k : Z → ℝ) (hF : Continuous F) (hH : Continuous H) (hk : Continuous k)
    (A B : ℝ≥0) (hA : ∀ z, ‖F z‖≤A) (hB : ∀ z, ‖H z‖≤B) :
    LipschitzWith (2*A*B) (affinePosteriorMean μ F H k) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜:=ℝ)
  · intro y
    exact (affinePosteriorMean_hasFDerivAt μ F H k hF hH hk y).differentiableAt
  · intro y
    exact_mod_cast affinePosteriorMean_fderiv_bound μ F H k hF hH hk A.property B.property hA hB y

end PersistencePays
#print axioms PersistencePays.affinePosteriorMean_lipschitz
