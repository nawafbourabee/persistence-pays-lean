import PersistencePays.CompactParameterIntegral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Differentiation of a compact exponential family with affine parameter.
This is the spatial derivative calculation for the free-flight posterior. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped InnerProductSpace
variable {E Z V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def affinePosteriorWeight (H : Z → E) (k : Z → ℝ) (y : E) (z : Z) : ℝ :=
  Real.exp (⟪H z,y⟫_ℝ+k z)

def affinePosteriorMean (μ : Measure Z) (F : Z → V) (H : Z → E) (k : Z → ℝ) (y : E) : V :=
  (∫ z, affinePosteriorWeight H k y z ∂μ)⁻¹ •
    ∫ z, affinePosteriorWeight H k y z • F z ∂μ

theorem affinePosteriorWeight_continuous (H : Z → E) (k : Z → ℝ)
    (hH : Continuous H) (hk : Continuous k) :
    Continuous (affinePosteriorWeight H k).uncurry := by
  unfold affinePosteriorWeight
  exact Real.continuous_exp.comp (((hH.comp continuous_snd).inner continuous_fst).add
    (hk.comp continuous_snd))

theorem affinePosteriorWeight_hasFDerivAt (H : Z → E) (k : Z → ℝ) (y : E) (z : Z) :
    HasFDerivAt (fun x => affinePosteriorWeight H k x z)
      (affinePosteriorWeight H k y z • innerSL ℝ (H z)) y := by
  exact (((innerSL ℝ (H z)).hasFDerivAt.add_const (k z)).exp)

theorem affinePosterior_integrals_derivative (μ : Measure Z) [IsFiniteMeasure μ]
    (F : Z → V) (H : Z → E) (k : Z → ℝ) (hF : Continuous F) (hH : Continuous H) (hk : Continuous k)
    (y : E) :
    HasFDerivAt (fun x => ∫ z, affinePosteriorWeight H k x z ∂μ)
      (∫ z, affinePosteriorWeight H k y z • innerSL ℝ (H z) ∂μ) y ∧
    HasFDerivAt (fun x => ∫ z, affinePosteriorWeight H k x z • F z ∂μ)
      (∫ z, affinePosteriorWeight H k y z • (innerSL ℝ (H z)).smulRight (F z) ∂μ) y := by
  have hw := affinePosteriorWeight_continuous H k hH hk
  have hi : Continuous (fun z => innerSL ℝ (H z)) := (innerSL ℝ).continuous.comp hH
  constructor
  · apply compact_parameter_integral_hasFDerivAt μ
      (F:=affinePosteriorWeight H k)
      (F':=fun x z => affinePosteriorWeight H k x z • (innerSL ℝ (H z) : E →L[ℝ] ℝ))
    · exact hw
    · exact hw.smul (hi.comp continuous_snd)
    · intro x z
      exact affinePosteriorWeight_hasFDerivAt H k x z
  · apply compact_parameter_integral_hasFDerivAt μ
      (F:=fun x z => affinePosteriorWeight H k x z • F z)
      (F':=fun x z => affinePosteriorWeight H k x z • (innerSL ℝ (H z)).smulRight (F z))
    · exact hw.smul (hF.comp continuous_snd)
    · exact hw.smul ((ContinuousLinearMap.smulRightL ℝ E V).continuous₂.comp₂ (hi.comp continuous_snd) (hF.comp continuous_snd))
    · intro x z
      have hd := (affinePosteriorWeight_hasFDerivAt H k x z).smul
        (hasFDerivAt_const (𝕜:=ℝ) (F z) x)
      convert hd using 1 <;> ext v <;> simp [smul_smul]

theorem affinePosterior_normalizer_pos (μ : Measure Z) [IsProbabilityMeasure μ]
    (H : Z → E) (k : Z → ℝ) (hH : Continuous H) (hk : Continuous k) (y : E) :
    0 < ∫ z, affinePosteriorWeight H k y z ∂μ := by
  apply integral_exp_pos
  exact ((affinePosteriorWeight_continuous H k hH hk).comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem affinePosteriorMean_hasFDerivAt (μ : Measure Z) [IsProbabilityMeasure μ]
    (F : Z → V) (H : Z → E) (k : Z → ℝ) (hF : Continuous F) (hH : Continuous H) (hk : Continuous k)
    (y : E) :
    let D := ∫ z, affinePosteriorWeight H k y z ∂μ
    let N := ∫ z, affinePosteriorWeight H k y z • F z ∂μ
    let D' := ∫ z, affinePosteriorWeight H k y z • innerSL ℝ (H z) ∂μ
    let N' := ∫ z, affinePosteriorWeight H k y z • (innerSL ℝ (H z)).smulRight (F z) ∂μ
    HasFDerivAt (affinePosteriorMean μ F H k) (D⁻¹ • N' - (D⁻¹)^2 • D'.smulRight N) y := by
  dsimp only
  have hd := affinePosterior_integrals_derivative μ F H k hF hH hk y
  have hp := affinePosterior_normalizer_pos μ H k hH hk y
  have hh := ((hasFDerivAt_inv hp.ne').comp y hd.1).smul hd.2
  convert hh using 1
  · ext x
    rfl
  · ext v
    simp
    module

end PersistencePays
#print axioms PersistencePays.affinePosteriorMean_hasFDerivAt
