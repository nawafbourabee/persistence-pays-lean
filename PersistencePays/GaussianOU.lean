import PersistencePays.Volume
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction

/-! The averaged OU update preserves the standard Gaussian law. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianOU (r σ : ℝ) (z : E × E) : E := r • z.1 + σ • z.2

/-- A normalized linear combination of independent standard Gaussian vectors
is again standard Gaussian; the independence is part of the product law. -/
theorem gaussianOU_preserving (r σ : ℝ) (hnorm : r ^ 2 + σ ^ 2 = 1) :
    MeasurePreserving (gaussianOU (E := E) r σ)
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  refine ⟨by unfold gaussianOU; fun_prop, ?_⟩
  have hmap : ((stdGaussian E).prod (stdGaussian E)).map (gaussianOU r σ) =
      (((stdGaussian E).map (fun v => r • v)).prod
        ((stdGaussian E).map (fun v => σ • v))).map (fun z => z.1 + z.2) := by
    rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap]
  let : IsProbabilityMeasure ((stdGaussian E).map (fun v => r • v)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure ((stdGaussian E).map (fun v => σ • v)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply, charFun_map_smul, charFun_stdGaussian]
  rw [← Complex.exp_add]
  congr 1
  have hr : (‖r • t‖ : ℂ) ^ 2 = (r : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast (show ‖r • t‖ ^ 2 = r ^ 2 * ‖t‖ ^ 2 by
      simp [norm_smul, mul_pow, sq_abs])
  have hs : (‖σ • t‖ : ℂ) ^ 2 = (σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast (show ‖σ • t‖ ^ 2 = σ ^ 2 * ‖t‖ ^ 2 by
      simp [norm_smul, mul_pow, sq_abs])
  have hc : (r : ℂ) ^ 2 + (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hnorm
  rw [hr, hs]
  calc
    _ = -((r : ℂ) ^ 2 + (σ : ℂ) ^ 2) * (‖t‖ : ℂ) ^ 2 / 2 := by ring
    _ = _ := by rw [hc]; ring

theorem ou_coefficients (a : ℝ) (ha : 0 ≤ a) :
    (Real.exp (-a)) ^ 2 + (Real.sqrt (1 - Real.exp (-2 * a))) ^ 2 = 1 := by
  have he : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sq_sqrt (sub_nonneg.mpr he)]
  have hx : Real.exp (-a) ^ 2 = Real.exp (-2 * a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hx]
  ring

theorem ou_halfStep_preserving (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) :
    MeasurePreserving
      (gaussianOU (E := E) (Real.exp (-γ * h / 2))
        (Real.sqrt (1 - Real.exp (-γ * h))))
      ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  apply gaussianOU_preserving
  have he₁ : -γ * h / 2 = -(γ * h / 2) := by ring
  have he₂ : -γ * h = -2 * (γ * h / 2) := by ring
  rw [he₁, he₂]
  exact ou_coefficients (γ * h / 2) (by positivity)

end PersistencePays

#print axioms PersistencePays.gaussianOU_preserving
#print axioms PersistencePays.ou_halfStep_preserving
