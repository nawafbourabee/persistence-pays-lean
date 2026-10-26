import PersistencePays.GaussianDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Gaussian integration by parts from mathlib's Euclidean integration by parts.
This supplies an analytic foundation for OU entropy dissipation; it does not
assert that dissipation or contraction has yet been proved. -/
open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma kinetic_hasFDerivAt (x : E) :
    HasFDerivAt (kineticPotential : E → ℝ) (innerSL ℝ x) x := by
  convert! (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1/2 : ℝ) using 1
  · funext y
    dsimp [kineticPotential]
    ring
  · ext v
    simp

lemma gaussian_weight_fderiv (x v : E) :
    fderiv ℝ (fun y : E => exp (-kineticPotential y)) x v =
      -⟪x, v⟫_ℝ * exp (-kineticPotential x) := by
  change (fderiv ℝ (fun y => exp ((-kineticPotential) y)) x) v = _
  rw [((kinetic_hasFDerivAt x).neg.exp).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    innerSL_apply_apply, smul_eq_mul, Pi.neg_apply]
  ring

lemma gaussian_integrable_iff_weighted (f : E → ℝ) :
    Integrable f (stdGaussian E) ↔
      Integrable (fun x => f x * exp (-kineticPotential x)) volume := by
  rw [stdGaussian_eq_kinetic_tilted]
  have hI : Integrable (fun x : E => exp ((-kineticPotential) x)) volume := kinetic_gibbs_integrable
  simpa only [Pi.neg_apply, smul_eq_mul, mul_comm] using integrable_tilted_iff hI f

lemma gaussian_integral_weighted (f : E → ℝ) :
    (∫ x, f x ∂stdGaussian E) =
      (∫ x, f x * exp (-kineticPotential x)) / (∫ x : E, exp (-kineticPotential x)) := by
  rw [stdGaussian_eq_kinetic_tilted, integral_tilted]
  simp only [Pi.neg_apply, smul_eq_mul]
  have he : (fun x : E => (exp (-kineticPotential x) / (∫ y : E, exp (-kineticPotential y))) * f x) =
      (fun x => (f x * exp (-kineticPotential x)) / (∫ y : E, exp (-kineticPotential y))) := by
    funext x
    ring
  rw [he, integral_div]

/-- Gaussian integration by parts under the explicit integrability hypotheses
needed for the Euclidean formula. -/
theorem gaussian_integration_by_parts (f : E → ℝ) (hfd : Differentiable ℝ f) (v : E)
    (hif : Integrable f (stdGaussian E))
    (hid : Integrable (fun x => fderiv ℝ f x v) (stdGaussian E))
    (hix : Integrable (fun x => f x * ⟪x, v⟫_ℝ) (stdGaussian E)) :
    (∫ x, f x * ⟪x, v⟫_ℝ ∂stdGaussian E) =
      ∫ x, fderiv ℝ f x v ∂stdGaussian E := by
  have hwf := (gaussian_integrable_iff_weighted f).mp hif
  have hwd := (gaussian_integrable_iff_weighted (fun x => fderiv ℝ f x v)).mp hid
  have hwx := (gaussian_integrable_iff_weighted (fun x => f x * ⟪x,v⟫_ℝ)).mp hix
  have hig : Integrable (fun x => f x * fderiv ℝ (fun y : E => exp (-kineticPotential y)) x v) volume := by
    simp_rw [gaussian_weight_fderiv]
    convert hwx.neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hwd hig hwf
    (fun x _ => hfd x) (fun x _ => ((kinetic_hasFDerivAt x).neg.exp).differentiableAt)
  simp_rw [gaussian_weight_fderiv] at hb
  have hidfun : (fun x => f x * (-⟪x,v⟫_ℝ * exp (-kineticPotential x))) =
      (fun x => -(f x * ⟪x,v⟫_ℝ * exp (-kineticPotential x))) := by funext x; ring
  rw [hidfun, integral_neg] at hb
  rw [gaussian_integral_weighted, gaussian_integral_weighted]
  congr 1
  linarith

end
end PersistencePays
#print axioms PersistencePays.gaussian_integration_by_parts
