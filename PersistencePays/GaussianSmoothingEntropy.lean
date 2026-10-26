import PersistencePays.PhaseGaussianRegularization
import PersistencePays.BoltzmannSemicontinuity

/-! Gaussian convolution has asymptotically no entropy cost. The proof is an
actual OU channel followed by a constant-Jacobian scaling, not a smoothness or
entropy-continuity premise. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fullGaussianOUKernel_energy_le (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (r σ : ℝ) (hn : r^2+σ^2=1) :
    (∫ z,phaseEnergy kineticPotential z ∂fullGaussianOUKernel r σ ∘ₘ μ) ≤
      2*((∫ z,‖z‖^2 ∂μ)+(∫ z,‖z‖^2 ∂(gaussianPairProbability (E:=E) : Measure (E×E)))) := by
  have hpost := fullGaussianOUKernel_memLp μ hμ r σ
  have hγ := gaussianPair_memLp (E:=E) 2 (by norm_num)
  have hbound : (∫ z,phaseEnergy kineticPotential z ∂fullGaussianOUKernel r σ ∘ₘ μ) ≤
      ∫ z,‖z‖^2 ∂fullGaussianOUKernel r σ ∘ₘ μ :=
    integral_mono (phaseGaussianEnergy_integrable _ hpost) hpost.integrable_norm_pow' phaseGaussianEnergy_le_norm
  apply hbound.trans
  rw [fullGaussianOUKernel_comp_map,integral_map (by fun_prop) (by fun_prop)]
  let ρ := μ.prod (gaussianPairProbability (E:=E) : Measure (E×E))
  have h1 : Integrable (fun z : (E×E)×(E×E) => ‖z.1‖^2) ρ := (hμ.comp_fst _).integrable_norm_pow'
  have h2 : Integrable (fun z : (E×E)×(E×E) => ‖z.2‖^2) ρ := (hγ.comp_snd μ).integrable_norm_pow'
  have hsum : Integrable (fun z : (E×E)×(E×E) => ‖r•z.1+σ•z.2‖^2) ρ :=
    (((hμ.comp_fst _).const_smul r).add ((hγ.comp_snd μ).const_smul σ)).integrable_norm_pow'
  have hr : |r|≤1 := (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith [sq_nonneg σ])
  have hσ : |σ|≤1 := (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith [sq_nonneg r])
  calc
    _ ≤ ∫ z : (E×E)×(E×E), 2*(‖z.1‖^2+‖z.2‖^2) ∂ρ := by
      apply integral_mono hsum ((h1.add h2).const_mul 2)
      intro z
      change ‖r•z.1+σ•z.2‖^2 ≤ 2*(‖z.1‖^2+‖z.2‖^2)
      have hl : ‖r•z.1+σ•z.2‖ ≤ ‖z.1‖+‖z.2‖ := by
        calc
          _ ≤ |r| *‖z.1‖+|σ| *‖z.2‖ := by simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (r•z.1) (σ•z.2)
          _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr)
            (mul_le_of_le_one_left (norm_nonneg _) hσ)
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hl
      nlinarith [sq_nonneg (‖z.1‖-‖z.2‖)]
    _ = _ := by
      rw [integral_const_mul,integral_add h1 h2,integral_fun_fst (fun z : E×E => ‖z‖^2),
        integral_fun_snd (fun z : E×E => ‖z‖^2),probReal_univ,one_smul,probReal_univ,one_smul]

theorem gaussianSmoothing_ou_scale (μ : ProbabilityMeasure (E×E)) (ε : ℝ)
    (s : ℝ) (hs : 0 < s) :
    ((fullGaussianOUKernel s⁻¹ (ε/s) ∘ₘ (μ : Measure (E×E))).map (phaseScaleEquiv s hs.ne')) =
      (additiveNoiseProbability μ gaussianPairProbability ε : Measure (E×E)) := by
  rw [fullGaussianOUKernel_comp_map,Measure.map_map (phaseScaleEquiv s hs.ne').measurable (by fun_prop),
    additiveNoiseProbability_coe]
  congr 1
  funext z
  simp only [Function.comp_def,phaseScaleEquiv_apply,smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  congr 1
  field_simp

theorem gaussianSmoothing_entropy_bound (μ : ProbabilityMeasure (E×E)) (ε : ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) :
    klDiv (additiveNoiseProbability μ gaussianPairProbability ε : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ ∧
    (klDiv (additiveNoiseProbability μ gaussianPairProbability ε : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E))).toReal ≤
    (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal +
      2*ε^2*((∫ z,‖z‖^2 ∂(μ : Measure (E×E)))+
        (∫ z,‖z‖^2 ∂(gaussianPairProbability (E:=E) : Measure (E×E)))) := by
  let s := Real.sqrt (1+ε^2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s^2 = 1+ε^2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by nlinarith [sq_nonneg ε]
  have hn : s⁻¹ ^ 2 + (ε/s)^2 = 1 := by
    field_simp
    nlinarith
  let ν := fullGaussianOUKernel s⁻¹ (ε/s) ∘ₘ (μ : Measure (E×E))
  have hν := fullGaussianOUKernel_memLp (μ : Measure (E×E)) hμ s⁻¹ (ε/s)
  have hKb := klDiv_step_le (fullGaussianOUKernel s⁻¹ (ε/s)) (μ : Measure (E×E))
    (gaussianPairProbability (E:=E) : Measure (E×E)) (fullGaussianOUKernel_invariant _ _ hn)
  have hKν : klDiv ν (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ := ne_top_of_le_ne_top hK hKb
  have hreal := ENNReal.toReal_mono hK hKb
  have hh := phaseGaussian_scale_entropy ν hν hKν s hs
  rw [gaussianSmoothing_ou_scale μ ε s hs] at hh
  refine ⟨hh.1,?_⟩
  rw [hh.2,hs2]
  have he := fullGaussianOUKernel_energy_le (μ : Measure (E×E)) hμ s⁻¹ (ε/s) hn
  have hp := mul_le_mul_of_nonneg_left he (sq_nonneg ε)
  have hl : 0 ≤ (2*(Module.finrank ℝ E:ℝ))*Real.log s := mul_nonneg (by positivity) (Real.log_nonneg hs1)
  change (klDiv ν _).toReal ≤ _ at hreal
  change (∫ z,phaseEnergy kineticPotential z ∂ν) ≤ _ at he
  change ε^2*(∫ z,phaseEnergy kineticPotential z ∂ν) ≤ _ at hp
  nlinarith

end PersistencePays
#print axioms PersistencePays.gaussianSmoothing_entropy_bound
