import PersistencePays.GaussianOU
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The standard Gaussian as a normalized kinetic Gibbs density

This mathlib-only proof adapts the Fourier argument in the read-only local
`CoupledJacobi/GaussianRadialLaw.lean`. The adaptation is checked anew here.
-/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Complex InnerProductSpace
open scoped RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def kineticPotential (v : E) : ℝ := ‖v‖ ^ 2 / 2

theorem gaussian_radial_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-a * ‖x‖ ^ 2)) volume := by
  have hi := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (a : ℂ)) (by simpa using ha) (0 : ℂ) (0 : E)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using hi.norm

theorem kinetic_gibbs_integrable :
    Integrable (fun v : E => Real.exp (-kineticPotential v)) volume := by
  convert gaussian_radial_integrable (E := E) (by norm_num : (0 : ℝ) < 1 / 2) using 1
  funext v
  congr 1
  dsimp [kineticPotential]
  ring

theorem kinetic_normalizer_complex :
    (((∫ v : E, Real.exp (-kineticPotential v)) : ℝ) : ℂ) =
      ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ ((Module.finrank ℝ E : ℂ) / 2) := by
  rw [← integral_complex_ofReal]
  convert GaussianFourier.integral_cexp_neg_mul_sq_norm (V := E) (b := (1 / 2 : ℂ))
    (by norm_num) using 1
  congr 1
  funext v
  simp only [kineticPotential, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  ring

theorem kinetic_tilted_charFun (t : E) :
    charFun (volume.tilted (-kineticPotential : E → ℝ)) t =
      Complex.exp (-‖t‖ ^ 2 / 2) := by
  let Z : ℝ := ∫ v : E, Real.exp (-kineticPotential v)
  have hZ : 0 < Z := integral_exp_pos kinetic_gibbs_integrable
  rw [charFun_apply, integral_tilted]
  change (∫ v : E, (Real.exp (-kineticPotential v) / Z) •
    Complex.exp ((⟪v, t⟫_ℝ : ℂ) * I)) = _
  have he : (fun v : E => (Real.exp (-kineticPotential v) / Z) •
      Complex.exp ((⟪v, t⟫_ℝ : ℂ) * I)) =
      (fun v => (Z : ℂ)⁻¹ * Complex.exp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + I * (⟪t, v⟫_ℝ : ℂ))) := by
    funext v
    rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_exp]
    calc
      _ = (Z : ℂ)⁻¹ * (Complex.exp (↑(-kineticPotential v)) *
          Complex.exp ((⟪v, t⟫_ℝ : ℂ) * I)) := by ring
      _ = _ := by
        rw [← Complex.exp_add, real_inner_comm v t]
        congr 2
        simp only [kineticPotential, Complex.ofReal_neg, Complex.ofReal_div,
          Complex.ofReal_pow, Complex.ofReal_ofNat]
        ring
  rw [he, integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)]
  rw [← kinetic_normalizer_complex]
  have hZne : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hex : I ^ 2 * (‖t‖ : ℂ) ^ 2 / (4 * (1 / 2 : ℂ)) = -(‖t‖ : ℂ) ^ 2 / 2 := by
    rw [Complex.I_sq]
    ring
  rw [hex]
  change (Z : ℂ)⁻¹ * ((Z : ℂ) * Complex.exp (-↑‖t‖ ^ 2 / 2)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hZne, one_mul]

theorem stdGaussian_eq_kinetic_tilted :
    stdGaussian E = volume.tilted (-kineticPotential : E → ℝ) := by
  let := isProbabilityMeasure_tilted (μ := (volume : Measure E)) kinetic_gibbs_integrable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, kinetic_tilted_charFun]

end PersistencePays

#print axioms PersistencePays.stdGaussian_eq_kinetic_tilted
