import PersistencePays.DensityCapFiniteEntropy
import PersistencePays.PhaseGaussianRegularization
import PersistencePays.FreeTransportGibbsEntropy
import PersistencePays.GaussianFlightConditional

/-! Gaussian smoothing has finite Gibbs entropy and all moments inherited from
the latent law. No absolute continuity or finite latent entropy is assumed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def smoothingDensityCap (ε:ℝ):ℝ :=
  |ε⁻¹|^Module.finrank ℝ E * |ε⁻¹|^Module.finrank ℝ E * heatConstant E 1^2

lemma smoothingDensityCap_pos {ε:ℝ} (hε:ε≠0) : 0<smoothingDensityCap (E:=E) ε := by
  unfold smoothingDensityCap
  exact mul_pos (mul_pos (pow_pos (abs_pos.mpr (inv_ne_zero hε)) _)
    (pow_pos (abs_pos.mpr (inv_ne_zero hε)) _))
    (sq_pos_of_pos (heatConstant_pos (by norm_num)))

theorem fullGaussianOUKernel_apply_density_cap (r ε:ℝ) (hε:ε≠0) (z:E×E) :
    fullGaussianOUKernel r ε z≤ENNReal.ofReal (smoothingDensityCap (E:=E) ε) •
      ((volume:Measure E).prod volume) := by
  let e:=triangularNoiseEquiv (r•z.1) (fun _=>r•z.2) measurable_const ε ε hε hε
  have he : fullGaussianOUKernel r ε z=((stdGaussian E).prod (stdGaussian E)).map e := by
    rw [fullGaussianOUKernel_apply]
    congr 1
  rw [he,triangularNoiseEquiv_density,←withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro w
  calc
    _≤triangularInverseJacobian (E:=E) ε ε*ENNReal.ofReal (heatConstant E 1^2):=
      mul_le_mul' le_rfl (gaussianPairDensity_le _)
    _=_:=by
      unfold triangularInverseJacobian smoothingDensityCap
      rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]

theorem fullGaussianOUKernel_density_cap (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (r ε:ℝ) (hε:ε≠0) :
    fullGaussianOUKernel r ε ∘ₘ μ≤ENNReal.ofReal (smoothingDensityCap (E:=E) ε) •
      ((volume:Measure E).prod volume) := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (fullGaussianOUKernel r ε).aemeasurable]
  calc
    _≤∫⁻ _ : E×E,(ENNReal.ofReal (smoothingDensityCap (E:=E) ε) •
        ((volume:Measure E).prod volume)) A ∂μ:=
      lintegral_mono (fun z=>fullGaussianOUKernel_apply_density_cap r ε hε z A)
    _=_:=by simp

theorem fullGaussianOUKernel_memLp_all (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {p:ℝ≥0∞} (hp:p≠∞) (hμ:MemLp id p μ) (r ε:ℝ) :
    MemLp id p (fullGaussianOUKernel r ε ∘ₘ μ) := by
  rw [fullGaussianOUKernel_comp_map]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  exact ((hμ.comp_fst _).const_smul r).add
    (((gaussianPair_memLp (E:=E) p hp).comp_snd μ).const_smul ε)

theorem A1.gaussianSmoothing_gibbs_entropy_finite {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (r ε:ℝ) (hε:ε≠0) : klDiv (fullGaussianOUKernel r ε ∘ₘ μ) (phaseGibbs U)≠∞ := by
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable]
  apply gibbs_entropy_finite_of_density_cap _ _
    (phase_gibbs_integrable U a.gibbs_integrable) _
    (a.phaseEnergy_integrable (fullGaussianOUKernel_memLp μ hμ r ε))
    (smoothingDensityCap (E:=E) ε) (smoothingDensityCap_pos hε)
    (fullGaussianOUKernel_density_cap μ r ε hε)

theorem A1.gaussianFlightLaw_entropy_finite {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (ε s:ℝ) (hε:ε≠0) : klDiv (gaussianFlightLaw μ ε s) (phaseGibbs U)≠∞ := by
  rw [gaussianFlightLaw_transport]
  exact a.freeTransport_gibbs_entropy_finite _ (fullGaussianOUKernel_memLp μ hμ 1 ε)
    (a.gaussianSmoothing_gibbs_entropy_finite μ hμ 1 ε hε) s

end PersistencePays
#print axioms PersistencePays.A1.gaussianSmoothing_gibbs_entropy_finite
#print axioms PersistencePays.A1.gaussianFlightLaw_entropy_finite
