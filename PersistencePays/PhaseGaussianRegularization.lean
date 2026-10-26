import PersistencePays.RegularizationConvergence
import PersistencePays.FiniteEntropyPropagation
import PersistencePays.ScaledVolumeEntropy
import PersistencePays.GibbsReferenceChange

/-! Gaussian regularization on the literal position--velocity product space. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianPairProbability : ProbabilityMeasure (E×E) :=
  ⟨(stdGaussian E).prod (stdGaussian E),inferInstance⟩

theorem gaussianPair_memLp (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p (gaussianPairProbability (E:=E) : Measure (E×E)) := by
  exact memLp_prod_iff.mpr ⟨(IsGaussian.memLp_id (stdGaussian E) p hp).comp_fst (stdGaussian E),
    (IsGaussian.memLp_id (stdGaussian E) p hp).comp_snd (stdGaussian E)⟩

def fullGaussianOUKernel (r σ : ℝ) : Kernel (E×E) (E×E) :=
  velocityOUKernel r σ ∥ₖ velocityOUKernel r σ

instance fullGaussianOUKernel_markov (r σ : ℝ) : IsMarkovKernel (fullGaussianOUKernel (E:=E) r σ) := by
  unfold fullGaussianOUKernel
  infer_instance

theorem fullGaussianOUKernel_invariant (r σ : ℝ) (hn : r^2+σ^2=1) :
    fullGaussianOUKernel r σ ∘ₘ (gaussianPairProbability (E:=E) : Measure (E×E)) =
      (gaussianPairProbability (E:=E) : Measure (E×E)) := by
  have he : fullGaussianOUKernel (E:=E) r σ =
      (Kernel.id ∥ₖ velocityOUKernel r σ) ∘ₖ (velocityOUKernel r σ ∥ₖ Kernel.id) := by
    rw [Kernel.parallelComp_id_left_comp_parallelComp,Kernel.comp_id]
    rfl
  rw [he,← Measure.comp_assoc]
  change (Kernel.id ∥ₖ velocityOUKernel r σ) ∘ₘ
    ((velocityOUKernel r σ ∥ₖ Kernel.id) ∘ₘ ((stdGaussian E).prod (stdGaussian E))) = _
  rw [← Measure.prod_comp_left,velocityOUKernel_invariant r σ hn,
    ← Measure.prod_comp_right,velocityOUKernel_invariant r σ hn]
  rfl

theorem fullGaussianOUKernel_apply (r σ : ℝ) (z : E×E) :
    fullGaussianOUKernel r σ z = (gaussianPairProbability (E:=E) : Measure (E×E)).map
      (fun η => r•z+σ•η) := by
  rw [fullGaussianOUKernel,Kernel.parallelComp_apply,velocityOUKernel_apply,velocityOUKernel_apply,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rfl

theorem fullGaussianOUKernel_comp_map (μ : Measure (E×E)) [SFinite μ] (r σ : ℝ) :
    fullGaussianOUKernel r σ ∘ₘ μ = (μ.prod (gaussianPairProbability (E:=E) : Measure (E×E))).map
      (fun z : (E×E)×(E×E) => r•z.1+σ•z.2) := by
  have he : fullGaussianOUKernel (E:=E) r σ = FiniteNoise.noiseKernel
      (gaussianPairProbability (E:=E) : Measure (E×E))
      (fun z : (E×E)×(E×E) => r•z.1+σ•z.2) (by fun_prop) := by
    ext z : 1
    rw [FiniteNoise.noiseKernel_apply,fullGaussianOUKernel_apply]
  rw [he,noiseKernel_comp]

theorem fullGaussianOUKernel_memLp (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (r σ : ℝ) :
    MemLp id 2 (fullGaussianOUKernel r σ ∘ₘ μ) := by
  rw [fullGaussianOUKernel_comp_map]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  exact ((hμ.comp_fst _).const_smul r).add
    (((gaussianPair_memLp (E:=E) 2 (by norm_num)).comp_snd μ).const_smul σ)

def phaseScaleEquiv (s : ℝ) (hs : s ≠ 0) : (E×E) ≃ᵐ (E×E) :=
  triangularNoiseEquiv 0 (fun _ => 0) measurable_const s s hs hs

theorem phaseScaleEquiv_apply (s : ℝ) (hs : s ≠ 0) (z : E×E) :
    phaseScaleEquiv s hs z = s•z := by
  simp only [phaseScaleEquiv,triangularNoiseEquiv,MeasurableEquiv.coe_mk,zero_add]
  rfl

theorem phaseGaussianEnergy_smul (s : ℝ) (z : E×E) :
    phaseEnergy kineticPotential (s•z) = s^2*phaseEnergy kineticPotential z := by
  simp only [phaseEnergy_eq_norm,kineticPotential,Prod.smul_fst,Prod.smul_snd,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem phaseGaussianEnergy_integrable (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : Integrable (phaseEnergy (kineticPotential : E → ℝ)) μ := by
  have he : phaseEnergy (kineticPotential : E → ℝ) = fun z => ‖z.1‖^2/2+‖z.2‖^2/2 := by
    funext z
    rw [phaseEnergy_eq_norm]
    rfl
  rw [he]
  exact (hμ.fst.integrable_norm_pow'.div_const 2).add (hμ.snd.integrable_norm_pow'.div_const 2)

theorem phaseGaussianEnergy_le_norm (z : E×E) :
    phaseEnergy kineticPotential z ≤ ‖z‖^2 := by
  rw [phaseEnergy_eq_norm]
  dsimp [kineticPotential]
  have h1 := norm_fst_le z
  have h2 := norm_snd_le z
  have hs1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h1
  have hs2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h2
  linarith

theorem phaseScale_inverseJacobian (s : ℝ) (hs : 0<s) :
    triangularInverseJacobian (E:=E) s s =
      ENNReal.ofReal (s⁻¹ ^ (2*Module.finrank ℝ E)) := by
  unfold triangularInverseJacobian
  rw [abs_of_pos (inv_pos.mpr hs),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show 2*Module.finrank ℝ E = Module.finrank ℝ E+Module.finrank ℝ E by omega,pow_add]

theorem phaseGaussian_scale_entropy (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hK : klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (s : ℝ) (hs : 0<s) :
    klDiv (μ.map (phaseScaleEquiv s hs.ne')) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞ ∧
    (klDiv (μ.map (phaseScaleEquiv s hs.ne')) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal =
      (klDiv μ (gaussianPairProbability (E:=E) : Measure (E×E))).toReal +
      (s^2-1)*(∫ z,phaseEnergy kineticPotential z ∂μ)-
        (2*(Module.finrank ℝ E:ℝ))*Real.log s := by
  have he : (volume.prod volume : Measure (E×E)).map (phaseScaleEquiv s hs.ne') =
      ENNReal.ofReal (s⁻¹^(2*Module.finrank ℝ E)) • (volume.prod volume : Measure (E×E)) := by
    rw [phaseScaleEquiv,triangularNoiseEquiv_map_volume,phaseScale_inverseJacobian s hs]
  have hdiff : (fun z => phaseEnergy kineticPotential (phaseScaleEquiv s hs.ne' z)-
      phaseEnergy kineticPotential z) = fun z => (s^2-1)*phaseEnergy (kineticPotential : E → ℝ) z := by
    funext z
    rw [phaseScaleEquiv_apply,phaseGaussianEnergy_smul]
    ring
  have hdiffi : Integrable (fun z => phaseEnergy kineticPotential (phaseScaleEquiv s hs.ne' z)-
      phaseEnergy (kineticPotential : E → ℝ) z) μ := by
    rw [hdiff]
    exact (phaseGaussianEnergy_integrable μ hμ).const_mul _
  have hh := scaled_volume_entropy_change (volume.prod volume : Measure (E×E))
    (phaseEnergy kineticPotential) (phaseEnergy_measurable kineticPotential (by unfold kineticPotential; fun_prop))
    (phase_gibbs_integrable kineticPotential kinetic_gibbs_integrable) μ
    (phaseScaleEquiv s hs.ne') (s⁻¹^(2*Module.finrank ℝ E)) (by positivity) he
    (by simpa only [gaussianPairProbability,ProbabilityMeasure.coe_mk,gaussianPair_eq_tilted] using hK) hdiffi
  rw [← gaussianPair_eq_tilted,hdiff,integral_const_mul,Real.log_pow,Real.log_inv] at hh
  refine ⟨hh.1,?_⟩
  change (klDiv (μ.map (phaseScaleEquiv s hs.ne')) ((stdGaussian E).prod (stdGaussian E))).toReal = _
  rw [hh.2]
  change _ = (klDiv μ ((stdGaussian E).prod (stdGaussian E))).toReal +
    (s^2-1)*(∫ z,phaseEnergy kineticPotential z ∂μ)-(2*(Module.finrank ℝ E:ℝ))*Real.log s
  push_cast
  ring

end PersistencePays
#print axioms PersistencePays.phaseGaussian_scale_entropy
