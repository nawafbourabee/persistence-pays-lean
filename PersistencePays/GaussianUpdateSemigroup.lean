import PersistencePays.GaussianReflection
import PersistencePays.KernelEntropy

/-! The actual OU probability-law transformation composes exactly. -/
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance gaussianUpdate_probability (r σ : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianUpdate r σ μ) :=
  Measure.isProbabilityMeasure_map (by unfold gaussianOU; fun_prop)

lemma charFun_gaussianUpdate (r σ : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    charFun (gaussianUpdate r σ μ) t =
      charFun μ (r • t) * Complex.exp (-((σ : ℂ)^2 * (‖t‖ : ℂ)^2)/2) := by
  have hm : gaussianUpdate r σ μ =
      ((μ.map (fun x => r • x)).prod
        ((stdGaussian E).map (fun y => σ • y))).map (fun z => z.1+z.2) := by
    rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  letI : IsProbabilityMeasure (μ.map (fun x => r • x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure ((stdGaussian E).map (fun y => σ • y)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [hm, charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply, charFun_map_smul, charFun_stdGaussian]
  congr 2
  have hh : (‖σ • t‖ : ℂ)^2 = (σ : ℂ)^2 * (‖t‖ : ℂ)^2 := by
    exact_mod_cast (show ‖σ • t‖^2 = σ^2*‖t‖^2 by simp [norm_smul, mul_pow, sq_abs])
  rw [hh]

theorem gaussianUpdate_comp (r₁ σ₁ r₂ σ₂ σ : ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (hσ : σ^2 = r₂^2*σ₁^2+σ₂^2) :
    gaussianUpdate r₂ σ₂ (gaussianUpdate r₁ σ₁ μ) =
      gaussianUpdate (r₂*r₁) σ μ := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianUpdate, charFun_gaussianUpdate, charFun_gaussianUpdate]
  have ht : r₁ • r₂ • t = (r₂*r₁) • t := by rw [smul_smul, mul_comm]
  rw [ht, mul_assoc, ← Complex.exp_add]
  congr 2
  have hh : (‖r₂ • t‖ : ℂ)^2 = (r₂ : ℂ)^2 * (‖t‖ : ℂ)^2 := by
    exact_mod_cast (show ‖r₂ • t‖^2 = r₂^2*‖t‖^2 by simp [norm_smul, mul_pow, sq_abs])
  have hc : (σ : ℂ)^2 = (r₂ : ℂ)^2*(σ₁ : ℂ)^2+(σ₂ : ℂ)^2 := by exact_mod_cast hσ
  rw [hh, hc]
  ring

theorem gaussianUpdate_entropy_le (r σ : ℝ) (hn : r^2+σ^2=1)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    klDiv (gaussianUpdate r σ μ) (stdGaussian E) ≤ klDiv μ (stdGaussian E) := by
  have h := klDiv_map_le (μ.prod (stdGaussian E))
    ((stdGaussian E).prod (stdGaussian E)) (show Measurable (gaussianOU r σ) by unfold gaussianOU; fun_prop)
  rw [(gaussianOU_preserving (E := E) r σ hn).map_eq] at h
  have hp : klDiv (μ.prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) =
      klDiv μ (stdGaussian E) := by
    simpa only [Measure.compProd_const] using
      klDiv_compProd_left μ (stdGaussian E) (Kernel.const E (stdGaussian E))
  exact h.trans_eq hp

end
end PersistencePays
#print axioms PersistencePays.gaussianUpdate_comp
#print axioms PersistencePays.gaussianUpdate_entropy_le
