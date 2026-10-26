import PersistencePays.ComparisonMidpoint
import PersistencePays.StartingEntropy

/-! Actual first-step energy and entropy estimates used in Section 6. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal InnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 800000

theorem A1.verlet_phaseEnergy_growth {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hL:h^2*L≤1/64) (z:E×E) :
    phaseEnergy U (verlet (gradient U) h z)≤(1.013:ℝ)*phaseEnergy U z := by
  have hnew := (lyapunov_energy_bounds a hstar hzero hL (verlet (gradient U) h z)).2.2.1
  have hstep := a.verlet_modifiedEnergy_growth hstar hzero hL z
  have hold := (lyapunov_energy_bounds a hstar hzero hL z).2.2.2
  have hnonneg := a.normalized_energy_nonnegative hstar hzero z
  nlinarith

theorem ou_phaseEnergy_integral (U:E→ℝ) (hU:Measurable U) (r σ:ℝ) (z:E×E) :
    (∫ w,phaseEnergy U w ∂phaseOUKernel r σ z)=
      U z.1+(r^2*‖z.2‖^2+σ^2*(Module.finrank ℝ E:ℝ))/2 := by
  rw [phaseOUKernel_apply,integral_map (by unfold OBABOPath.ou; fun_prop)
    (phaseEnergy_measurable U hU).aestronglyMeasurable]
  have hm : MemLp (fun ξ:E=>r•z.2+σ•ξ) 2 (stdGaussian E) :=
    (memLp_const (μ:=stdGaussian E) (p:=2) (r•z.2)).add
      ((IsGaussian.memLp_two_id (μ:=stdGaussian E)).const_smul σ)
  have he (ξ:E) : phaseEnergy U (OBABOPath.ou r σ ξ z)=U z.1+‖r•z.2+σ•ξ‖^2/2 := by
    rw [phaseEnergy_eq_norm]; rfl
  simp_rw [he]
  rw [integral_add (integrable_const _) (hm.integrable_norm_pow'.div_const 2),
    integral_const,probReal_univ,one_smul,integral_div,stdGaussian_affine_norm_square,
    norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem A1.ou_phaseEnergy_le {U:E→ℝ} {m L h r σ:ℝ} (a:A1 U m L)
    (hr:r^2≤1) (hσ:σ^2≤2*h) (z:E×E) :
    (∫ w,phaseEnergy U w ∂phaseOUKernel r σ z) ≤
      phaseEnergy U z+h*(Module.finrank ℝ E:ℝ) := by
  rw [ou_phaseEnergy_integral U a.twice_contDiff.continuous.measurable,phaseEnergy_eq_norm]
  have hv:=mul_le_mul_of_nonneg_right hr (sq_nonneg ‖z.2‖)
  have hd:=mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg (Module.finrank ℝ E): (0:ℝ)≤_)
  nlinarith

theorem A1.ou_phaseEnergy_comp_le {U:E→ℝ} {m L h r σ:ℝ} (a:A1 U m L)
    (hr:r^2≤1) (hσ:σ^2≤2*h)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ) :
    (∫ w,phaseEnergy U w ∂phaseOUKernel r σ ∘ₘ μ) ≤
      (∫ z,phaseEnergy U z ∂μ)+h*(Module.finrank ℝ E:ℝ) := by
  have hν:=phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  have hi:=a.phaseEnergy_integrable hν
  have hμi:=a.phaseEnergy_integrable hμ
  simp only [id_eq] at hi hμi
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  calc
    _ ≤ ∫ z,phaseEnergy U z+h*(Module.finrank ℝ E:ℝ) ∂μ :=
      integral_mono hi.integral_comp (hμi.add (integrable_const _)) (a.ou_phaseEnergy_le hr hσ)
    _ = _ := by
      rw [integral_add hμi (integrable_const _),integral_const,probReal_univ,one_smul]

theorem A1.unadjusted_phaseEnergy_comp_le {U:E→ℝ} {L h r σ:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hL:h^2*L≤1/64)
    (hr:r^2≤1) (hσ:σ^2≤2*h)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let K := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ
    (∫ w,phaseEnergy U w ∂K ∘ₘ μ) ≤
      (1.013:ℝ)*((∫ z,phaseEnergy U z ∂μ)+h*(Module.finrank ℝ E:ℝ))+
        h*(Module.finrank ℝ E:ℝ) := by
  dsimp only
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ν := phaseOUKernel r σ ∘ₘ μ
  let D := verlet (gradient U) h
  have hD:Measurable D := (verlet_measurePreserving (gradient U) hg h).measurable
  have hν:MemLp id 2 ν := phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ
  letI:IsProbabilityMeasure (ν.map D) := Measure.isProbabilityMeasure_map hD.aemeasurable
  have hDν:MemLp id 2 (ν.map D) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hD.aemeasurable).mpr (a.verlet_memLp hν h)
  have h1:=a.ou_phaseEnergy_comp_le hr hσ μ hμ
  have h3:=a.ou_phaseEnergy_comp_le hr hσ (ν.map D) hDν
  have h2:(∫ w,phaseEnergy U w ∂ν.map D)≤(1.013:ℝ)*(∫ w,phaseEnergy U w ∂ν) := by
    rw [integral_map hD.aemeasurable (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable).aestronglyMeasurable,
      ←integral_const_mul]
    exact integral_mono (a.phaseEnergy_integrable (a.verlet_memLp hν h))
      ((a.phaseEnergy_integrable hν).const_mul _) (a.verlet_phaseEnergy_growth hstar hzero hL)
  rw [unadjustedStepKernel_eq_sandwich,gaussianSandwichKernel_comp]
  change (∫ w,phaseEnergy U w ∂phaseOUKernel r σ ∘ₘ (ν.map D))≤_
  change (∫ w,phaseEnergy U w ∂ν)≤_ at h1
  nlinarith

theorem A1.unadjusted_start_energy {U:E→ℝ} {L h R:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0<h) (hL:h^2*L≤1/64)
    (z:E×E) (hz:phaseEnergy U z≤R) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let K := OBABOPath.unadjustedStepKernel (gradient U) hg h (Real.exp (-h))
      (Real.sqrt (1-Real.exp (-2*h)))
    (∫ w,phaseEnergy U w ∂K z)≤(1.02:ℝ)*R+(0.27:ℝ)*(Module.finrank ℝ E:ℝ) := by
  dsimp only
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  have hc:=normalized_ou_coefficients h hh.le
  have hr:r^2≤1 := by
    have hn:r^2+σ^2=1 := hc.2.2.2.1
    nlinarith [sq_nonneg σ]
  have hσ:σ^2≤2*h := hc.2.2.2.2.2.2.2
  have hb:=a.unadjusted_phaseEnergy_comp_le hstar hzero hL hr hσ (Measure.dirac z) (memLp_id_dirac z 2)
  dsimp only at hb
  rw [kernel_comp_dirac,integral_dirac] at hb
  have hR:0≤R := (a.normalized_energy_nonnegative hstar hzero z).trans hz
  have hhsq:=mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg h)
  have hmax:h≤1/8 := by nlinarith
  have hhd:=mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg (Module.finrank ℝ E):(0:ℝ)≤_)
  nlinarith

end PersistencePays
#print axioms PersistencePays.A1.unadjusted_start_energy
