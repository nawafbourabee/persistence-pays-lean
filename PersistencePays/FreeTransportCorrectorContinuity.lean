import PersistencePays.CorrectorGraphLaw
import PersistencePays.TransportEntropySemicontinuity
import PersistencePays.FiniteMoments

/-! Corrector continuity along the actual free flight, with a shared-latent-state
coupling and exact quadratic transport cost bound. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem freeTransport_norm_le (s : ℝ) (z : E×E) :
    ‖freeTransport s z‖ ≤ (1+|s|)*‖z‖ := by
  change max ‖z.1+s•z.2‖ ‖z.2‖ ≤ _
  apply max_le
  · calc
      _ ≤ ‖z.1‖+|s| *‖z.2‖ := by simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le z.1 (s•z.2)
      _ ≤ ‖z‖+|s| *‖z‖ := add_le_add (norm_fst_le z) (mul_le_mul_of_nonneg_left (norm_snd_le z) (abs_nonneg _))
      _ = _ := by ring
  · exact (norm_snd_le z).trans (by nlinarith [mul_nonneg (abs_nonneg s) (norm_nonneg z)])

theorem transportProbability_memLp (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hμ : MemLp id p μ) (s : ℝ) :
    MemLp id p (transportProbability μ s : Measure (E×E)) :=
  (memLp_map_measure_iff measurable_id.aestronglyMeasurable (measurable_freeTransport s).aemeasurable).mpr
    (drift_memLp hμ s)

theorem freeTransport_moment_tendsto (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (sn : ℕ → ℝ) {s : ℝ} (hs : Tendsto sn atTop (𝓝 s)) :
    Tendsto (fun n => ∫ z,‖z‖^2 ∂(transportProbability μ (sn n) : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(transportProbability μ s : Measure (E×E)))) := by
  have he (t : ℝ) : (∫ z,‖z‖^2 ∂(transportProbability μ t : Measure (E×E))) =
      ∫ z,‖freeTransport t z‖^2 ∂μ := integral_map (measurable_freeTransport t).aemeasurable (by fun_prop)
  simp_rw [he]
  obtain ⟨C,hC,hbound⟩ := (Metric.isBounded_range_of_tendsto sn hs).exists_pos_norm_le
  apply tendsto_integral_of_dominated_convergence (fun z : E×E => (1+C)^2*‖z‖^2)
    (fun n => by unfold freeTransport drift; fun_prop) (hμ.integrable_norm_pow'.const_mul _)
  · intro n
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : |sn n| ≤ C := by simpa only [Real.norm_eq_abs] using hbound (sn n) (mem_range_self n)
    have hh := (freeTransport_norm_le (sn n) z).trans
      (mul_le_mul_of_nonneg_right (by linarith : 1+|sn n|≤1+C) (norm_nonneg z))
    have hh2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
    simpa only [mul_pow] using hh2
  · apply Filter.Eventually.of_forall
    intro z
    apply (show Continuous (fun t : ℝ => ‖freeTransport t z‖^2) by unfold freeTransport drift; fun_prop).continuousAt.tendsto.comp hs

def freeTransportCoupling (μ : Measure (E×E)) [IsProbabilityMeasure μ] (s t : ℝ) :
    ProbabilityMeasure ((E×E)×(E×E)) :=
  ⟨μ.map (fun z => (freeTransport s z,freeTransport t z)),Measure.isProbabilityMeasure_map
    ((measurable_freeTransport s).prodMk (measurable_freeTransport t)).aemeasurable⟩

theorem freeTransportCoupling_mem (μ : Measure (E×E)) [IsProbabilityMeasure μ] (s t : ℝ) :
    freeTransportCoupling μ s t ∈ QuadraticTransport.plans (transportProbability μ s) (transportProbability μ t) := by
  constructor <;> apply Subtype.ext
  · change (μ.map (fun z => (freeTransport s z,freeTransport t z))).map Prod.fst = _
    rw [Measure.map_map measurable_fst ((measurable_freeTransport s).prodMk (measurable_freeTransport t))]
    rfl
  · change (μ.map (fun z => (freeTransport s z,freeTransport t z))).map Prod.snd = _
    rw [Measure.map_map measurable_snd ((measurable_freeTransport s).prodMk (measurable_freeTransport t))]
    rfl

theorem freeTransport_norm_sub_sq (s t : ℝ) (z : E×E) :
    ‖freeTransport s z-freeTransport t z‖^2 = (s-t)^2*‖z.2‖^2 := by
  have he : freeTransport s z-freeTransport t z = ((s-t)•z.2,0) := by
    ext <;> simp [freeTransport,drift,sub_smul] <;> abel
  rw [he,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _),norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem freeTransport_cost_le (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (s t : ℝ) :
    (QuadraticTransport.cost (transportProbability μ s) (transportProbability μ t)).toReal ≤
      (s-t)^2*(∫ z,‖z.2‖^2 ∂μ) := by
  have hp := freeTransportCoupling_mem μ s t
  have hi := QuadraticTransport.squaredCost_integrable _ _ _ hp
    (transportProbability_memLp μ hμ s).integrable_norm_pow'
    (transportProbability_memLp μ hμ t).integrable_norm_pow'
  have hf := QuadraticTransport.squaredCost_finite _ _ _ hp
    (transportProbability_memLp μ hμ s).integrable_norm_pow'
    (transportProbability_memLp μ hμ t).integrable_norm_pow'
  have hlo : QuadraticTransport.cost (transportProbability μ s) (transportProbability μ t) ≤
      QuadraticTransport.squaredCost (freeTransportCoupling μ s t) := iInf₂_le _ hp
  apply (ENNReal.toReal_mono hf hlo).trans_eq
  unfold QuadraticTransport.squaredCost
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z : (E×E)×(E×E) => sq_nonneg ‖z.1-z.2‖)) hi.aestronglyMeasurable]
  change (∫ z,‖z.1-z.2‖^2 ∂μ.map (fun z => (freeTransport s z,freeTransport t z))) = _
  rw [integral_map ((measurable_freeTransport s).prodMk (measurable_freeTransport t)).aemeasurable (by fun_prop)]
  simp_rw [freeTransport_norm_sub_sq]
  exact integral_const_mul _ _

theorem freeTransport_cost_tendsto (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (sn : ℕ → ℝ) {s : ℝ} (hs : Tendsto sn atTop (𝓝 s)) :
    Tendsto (fun n => (QuadraticTransport.cost (transportProbability μ (sn n)) (transportProbability μ s)).toReal)
      atTop (𝓝 0) := by
  have hh := ((hs.sub_const s).pow 2).mul_const (∫ z,‖z.2‖^2 ∂μ)
  simp only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul] at hh
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => freeTransport_cost_le μ hμ (sn n) s) hh

/-- Continuity holds for every finite-second-moment phase law with a density;
finite relative entropy is not needed for this conclusion. -/
theorem continuous_freeTransport_corrector (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ : ProbabilityMeasure E) (hμ : MemLp id 2 μ) (hξ : MemLp id 2 (ξ : Measure E))
    (hac : μ ≪ (volume : Measure E).prod volume) :
    Continuous (fun t : ℝ => transportCorrector (transportJoint μ t) ξ) := by
  apply SeqContinuous.continuous
  intro sn s hs
  have ha (t : ℝ) : (transportJoint μ t).fst ≪ (volume : Measure E) := by
    change transportPosition μ t ≪ volume
    rw [transportPosition_eq_withDensity μ hac t]
    exact withDensity_absolutelyContinuous _ _
  exact transportCorrector_stability (fun n => transportProbability μ (sn n)) (transportProbability μ s) ξ
    (fun n => transportProbability_memLp μ hμ (sn n)) (transportProbability_memLp μ hμ s) hξ
    (fun n => ha (sn n)) (ha s) ((continuous_transportProbability μ).continuousAt.tendsto.comp hs)
    (freeTransport_moment_tendsto μ hμ sn hs) (freeTransport_cost_tendsto μ hμ sn hs)

end PersistencePays
#print axioms PersistencePays.continuous_freeTransport_corrector
