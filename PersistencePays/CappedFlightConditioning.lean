import PersistencePays.CappedFlight
import PersistencePays.ConditioningEntropy

/-! Exact conditional-law identities for the unreversed part of the capped flight. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

section General
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem cond_map (μ : Measure S) (f:S→T) (hf:Measurable f) (A:Set T) (hA:MeasurableSet A) :
    cond (μ.map f) A=(cond μ (f⁻¹' A)).map f := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul,Measure.map_apply hf hA,Measure.restrict_map hf hA]

theorem cond_ae_mem (μ : Measure S) (A:Set S) (hA:MeasurableSet A) :
    ∀ᵐ x ∂cond μ A,x∈A :=
  ((Measure.AbsolutelyContinuous.refl (μ.restrict A)).smul_left _).ae_le (ae_restrict_mem hA)
end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def fastVelocitySet (vstar:ℝ) : Set (E×E) := {z|vstar<‖z.2‖}

theorem fastVelocitySet_measurable (vstar:ℝ) : MeasurableSet (fastVelocitySet (E:=E) vstar) :=
  measurableSet_lt measurable_const measurable_snd.norm

theorem cappedFlight_fast_preimage (h vstar s:ℝ) :
    (cappedFlightEquiv (E:=E) h vstar s)⁻¹' fastVelocitySet vstar=fastVelocitySet vstar := by
  ext z
  simp only [mem_preimage,fastVelocitySet,mem_setOf_eq,cappedFlight_snd_norm]

theorem cappedFlight_fast_mass (μ:Measure (E×E)) (h vstar s:ℝ) :
    cappedFlightLaw μ h vstar s (fastVelocitySet vstar)=μ (fastVelocitySet vstar) := by
  rw [cappedFlightLaw,Measure.map_apply (cappedFlightEquiv h vstar s).measurable
    (fastVelocitySet_measurable vstar),cappedFlight_fast_preimage]

theorem cappedFlight_slow_cond (μ:Measure (E×E)) (h vstar s:ℝ) :
    cond (cappedFlightLaw μ h vstar s) (fastVelocitySet vstar)ᶜ=
      transportJoint (cond μ (fastVelocitySet vstar)ᶜ) s := by
  rw [cappedFlightLaw,cond_map μ _ (cappedFlightEquiv h vstar s).measurable _
    (fastVelocitySet_measurable vstar).compl,preimage_compl,cappedFlight_fast_preimage]
  unfold transportJoint
  apply Measure.map_congr
  filter_upwards [cond_ae_mem μ _ (fastVelocitySet_measurable vstar).compl] with z hz
  apply cappedFlight_slow
  exact not_lt.mp hz

theorem cappedFlight_fast_cond (μ:Measure (E×E)) (h vstar s:ℝ) :
    cond (cappedFlightLaw μ h vstar s) (fastVelocitySet vstar)=
      (cond μ (fastVelocitySet vstar)).map (cappedFlightEquiv h vstar s) := by
  rw [cappedFlightLaw,cond_map μ _ (cappedFlightEquiv h vstar s).measurable _
    (fastVelocitySet_measurable vstar),cappedFlight_fast_preimage]

/-- Pointwise no-overshoot for the capped flight, with the exceptional conditional
entropy kept explicitly. Conditioning laws and endpoint masses are actual laws. -/
theorem A1.cappedFlight_entropy_no_overshoot {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) {h vstar s:ℝ} (hh : 0 < h) (hs : 0 ≤ s) (hsh : s ≤ h)
    (hpos:μ (fastVelocitySet vstar)≠0) (hcomp:μ (fastVelocitySet vstar)ᶜ≠0) :
    let α := (μ (fastVelocitySet vstar)).toReal
    let p := cappedFlightLaw μ h vstar
    (conditionalGaussianEntropy (p s) (stdGaussian E) 0).toReal ≤
      (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
      (conditionalGaussianEntropy (p h) (stdGaussian E) 0).toReal+2*binaryEntropy α+
      α*(conditionalGaussianEntropy (cond (p s) (fastVelocitySet vstar)) (stdGaussian E) 0).toReal := by
  let A := fastVelocitySet (E:=E) vstar
  let p := cappedFlightLaw μ h vstar
  let α := (μ A).toReal
  have hA := fastVelocitySet_measurable (E:=E) vstar
  have hm (u:ℝ) : p u A=μ A := cappedFlight_fast_mass μ h vstar u
  have hmc (u:ℝ) : p u Aᶜ=μ Aᶜ := by
    rw [measure_compl hA (measure_ne_top _ _),measure_compl hA (measure_ne_top _ _)]
    simp only [measure_univ]
    change 1-p u A=1-μ A
    rw [hm]
  have he (u:ℝ) : conditionalGaussianEntropy (p u) (stdGaussian E) 0≠∞ :=
    a.velocity_entropy_finite _ (a.cappedFlight_entropy_finite μ hμ hK h vstar u)
  have h0 := lemma_5_8 μ (a.velocity_entropy_finite μ hK) A hA hpos hcomp
  have hhE := lemma_5_8 (p h) (he h) A hA (by rwa [hm]) (by rwa [hmc])
  have hsE := lemma_5_8 (p s) (he s) A hA (by rwa [hm]) (by rwa [hmc])
  let ν := cond μ Aᶜ
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hcomp
  have hν : conditionalGaussianEntropy ν (stdGaussian E) 0≠∞ := by
    have ht := conditioning_entropy_finite μ (stdGaussian E)
      (by simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] using a.velocity_entropy_finite μ hK)
      Aᶜ hA.compl hcomp
    simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] using ht
  have hνh : conditionalGaussianEntropy ν (stdGaussian E) h≠∞ := by
    have hc := conditioning_entropy_finite (p h) (stdGaussian E)
      (by simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] using he h)
      Aᶜ hA.compl (by rwa [hmc])
    rw [cappedFlight_slow_cond] at hc
    simpa only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition] using hc
  have hn := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hν,hνh⟩)
    (corollary_3_5 ν hh hs hsh)
  rw [ENNReal.toReal_add hν hνh] at hn
  have hα1 : α ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞)≠∞) (prob_le_one (μ:=μ) (s:=A)))
  have hn' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hα1)
  dsimp only at h0 hhE hsE ⊢
  rw [hm] at hhE hsE
  rw [cappedFlight_slow_cond] at hhE hsE
  have hz0 : 0≤(conditionalGaussianEntropy (cond μ A) (stdGaussian E) 0).toReal := ENNReal.toReal_nonneg
  have hzh : 0≤(conditionalGaussianEntropy (cond (p h) A) (stdGaussian E) 0).toReal := ENNReal.toReal_nonneg
  have hα0 : 0≤α := ENNReal.toReal_nonneg
  change (1-α)*(conditionalGaussianEntropy ν (stdGaussian E) s).toReal ≤
    (1-α)*((conditionalGaussianEntropy ν (stdGaussian E) 0).toReal+
      (conditionalGaussianEntropy ν (stdGaussian E) h).toReal) at hn'
  dsimp only [ν,α,A,p] at *
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition] at *
  nlinarith [mul_nonneg hα0 hz0,mul_nonneg hα0 hzh,h0.1,hhE.1,hsE.2]

end PersistencePays
#print axioms PersistencePays.A1.cappedFlight_entropy_no_overshoot
