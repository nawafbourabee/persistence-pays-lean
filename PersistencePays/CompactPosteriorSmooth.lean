import PersistencePays.CompactMixtureSmooth
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Smooth normalized expectations for a compact latent law. This supplies
the analytic part of the Gaussian-mixture posterior calculation; identifying
that posterior with the actual conditional law is a separate Bayes identity. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
universe u
variable {P Y Z V : Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def compactPosteriorMean (μ : Measure Z) (g : Z → Y)
    (ψ : P×Y → ℝ) (F : P×Y → V) (x : P) : V :=
  (∫ z, Real.exp (ψ (x,g z)) ∂μ)⁻¹ • ∫ z, Real.exp (ψ (x,g z)) • F (x,g z) ∂μ

theorem compactPosterior_normalizer_pos (μ : Measure Z) [IsProbabilityMeasure μ]
    (g : Z → Y) (hg : Continuous g) (ψ : P×Y → ℝ) (hψ : Continuous ψ) (x : P) :
    0 < ∫ z, Real.exp (ψ (x,g z)) ∂μ := by
  apply integral_exp_pos
  exact (Real.continuous_exp.comp (hψ.comp (continuous_const.prodMk hg))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem compactPosteriorMean_contDiff (n : ℕ) (μ : Measure Z) [IsProbabilityMeasure μ]
    (g : Z → Y) (hg : Continuous g) (ψ : P×Y → ℝ) (hψ : ContDiff ℝ n ψ)
    (F : P×Y → V) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (compactPosteriorMean μ g ψ F) := by
  have hden := compact_mixture_integral_contDiff_real n μ g hg (fun q => Real.exp (ψ q)) hψ.exp
  have hnum := compact_mixture_integral_contDiff n μ g hg (fun q => Real.exp (ψ q) • F q)
    (hψ.exp.smul hF)
  exact (hden.inv (fun x => (compactPosterior_normalizer_pos μ g hg ψ hψ.continuous x).ne')).smul hnum

theorem compactPosteriorMean_eq_tilted (μ : Measure Z) [IsProbabilityMeasure μ]
    (g : Z → Y) (ψ : P×Y → ℝ) (F : P×Y → V) (x : P) :
    compactPosteriorMean μ g ψ F x =
      ∫ z, F (x,g z) ∂μ.tilted (fun z => ψ (x,g z)) := by
  rw [integral_tilted]
  unfold compactPosteriorMean
  rw [← integral_smul]
  congr 1
  funext z
  rw [smul_smul,div_eq_inv_mul]

theorem compactPosteriorMean_norm_le (μ : Measure Z) [IsProbabilityMeasure μ]
    (g : Z → Y) (hg : Continuous g) (ψ : P×Y → ℝ) (hψ : Continuous ψ)
    (F : P×Y → V) (x : P) (B : ℝ) (hb : ∀ z, ‖F (x,g z)‖ ≤ B) :
    ‖compactPosteriorMean μ g ψ F x‖ ≤ B := by
  have hi : Integrable (fun z => Real.exp (ψ (x,g z))) μ :=
    (Real.continuous_exp.comp (hψ.comp (continuous_const.prodMk hg))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  letI : IsProbabilityMeasure (μ.tilted (fun z => ψ (x,g z))) := isProbabilityMeasure_tilted hi
  rw [compactPosteriorMean_eq_tilted]
  simpa only [probReal_univ,one_mul,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=μ.tilted (fun z => ψ (x,g z))) (Filter.Eventually.of_forall hb)

end PersistencePays
#print axioms PersistencePays.compactPosteriorMean_contDiff
#print axioms PersistencePays.compactPosteriorMean_norm_le
