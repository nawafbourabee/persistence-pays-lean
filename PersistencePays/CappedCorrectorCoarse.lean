import PersistencePays.CappedEntropyIntegral
import PersistencePays.CappedKickBalance

/-! The full capped-flight corrector estimate in the post-first-kick coordinates. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.cappedFlight_entropy_balance {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) {h vstar:ℝ} (hh:0 < h) :
    boltzmannEntropy (cappedFlightLaw μ h vstar h).fst+
      (conditionalGaussianEntropy (cappedFlightLaw μ h vstar h) (stdGaussian E) 0).toReal=
    boltzmannEntropy μ.fst+(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal := by
  let mid := transportJoint μ (h/2)
  let plus := cappedMidpointLaw μ h vstar
  have hb0 := (a.free_transport_entropy_balance μ hμ hK (h/2)).2.2
  have hb1 := (a.free_transport_entropy_balance plus (cappedMidpointLaw_memLp μ hμ h vstar)
    (a.cappedMidpoint_entropy_finite μ hμ hK h vstar) (h/2)).2.2
  have hE : conditionalGaussianEntropy plus (stdGaussian E) 0=
      conditionalGaussianEntropy μ (stdGaussian E) (h/2) := by
    rw [show plus=mid.map (speedFlipEquiv vstar) from rfl,speedFlip_conditional_entropy]
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition]
    rfl
  have hL : plus.fst=mid.fst := map_position_preserving_fst mid (speedFlipEquiv vstar) (speedFlip_fst vstar)
  rw [hE,hL] at hb1
  rw [cappedFlightLaw_endpoint μ hh]
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition] at hb0 hb1 ⊢
  change boltzmannEntropy (transportJoint plus (h/2)).fst+
    (klDiv (transportJoint plus (h/2)) ((transportJoint plus (h/2)).fst.prod (stdGaussian E))).toReal=_
  nlinarith

theorem A1.capped_corrector_flight_coarse {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar:ℝ) (hpos:μ (fastVelocitySet vstar)≠0) (hcomp:μ (fastVelocitySet vstar)ᶜ≠0) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let pre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let final := cappedFlightLaw μ h vstar h
    let post := final.map (kickEquiv (gradient U) hg (h/2))
    a.corrector post-a.corrector pre ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy pre (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy post (stdGaussian E) 0).toReal)-
        (1/2:ℝ)*(klDiv μ.fst (positionGibbs U)).toReal)+
      h*((13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂μ)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂μ)+
        7*cappedMidEntropyError U μ D vstar)+
      2*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂μ)*
        QuadraticTransport.wassersteinTwo ⟨(transportJoint μ (h/2)).fst,inferInstance⟩ a.targetProbability := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let final := cappedFlightLaw μ h vstar h
  have hf := cappedFlightLaw_memLp μ hμ h vstar h
  have hKf := a.cappedFlight_entropy_finite μ hμ hK h vstar h
  have hk0 := a.lemma_4_3 μ hμ hK (-h/2)
  have hk1 := a.lemma_4_3 final hf hKf (h/2)
  have hfly := a.capped_free_corrector_bound (vstar:=vstar) hsm μ hμ hK hh
  have hI := a.cappedEntropyIntegral_bound hstar hzero hh hL μ hμ hK D hD hcap vstar hpos hcomp
  have hbalance := a.cappedFlight_entropy_balance (vstar:=vstar) μ hμ hK hh
  have hkick := (a.capped_paired_kick_entropy μ h vstar hh hμ hK).2.2
  have hgap0 := (a.transportGap_identity μ hμ hK).2.1
  have hgap1 := (a.transportGap_identity final hf hKf).2.1
  have hEx : 0≤(klDiv final.fst (positionGibbs U)).toReal := ENNReal.toReal_nonneg
  dsimp only at hk0 hk1 hkick ⊢
  change a.corrector (μ.map (kickEquiv (gradient U) hg (-h/2)))=_ at hk0
  change a.corrector (final.map (kickEquiv (gradient U) hg (h/2)))=_ at hk1
  change a.corrector final-a.corrector μ≤_ at hfly
  change boltzmannEntropy final.fst+_=_ at hbalance
  have hkickh := mul_le_mul_of_nonneg_left hkick (show 0 ≤ (13/2:ℝ)*h by positivity)
  have hbalanceh := congrArg (fun x:ℝ=>h*x) hbalance
  dsimp only [final,hg,fastVelocitySet] at *
  nlinarith [mul_nonneg hh.le hgap0,mul_nonneg hh.le hgap1,mul_nonneg hh.le hEx]

theorem cappedFlightLaw_eq_transport_of_fast_null (μ:Measure (E×E)) (h vstar s:ℝ)
    (hzero:μ (fastVelocitySet vstar)=0) : cappedFlightLaw μ h vstar s=transportJoint μ s := by
  apply Measure.map_congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
  exact cappedFlight_slow (not_lt.mp hz)

theorem cappedMidEntropyError_of_fast_null (U:E→ℝ) (μ:Measure (E×E)) (D vstar:ℝ)
    (hzero:μ (fastVelocitySet vstar)=0) : cappedMidEntropyError U μ D vstar=0 := by
  have hr : μ.restrict (fastVelocitySet vstar)=0 := Measure.restrict_eq_zero.mpr hzero
  simp only [cappedMidEntropyError,hzero,ENNReal.toReal_zero,mul_zero,zero_mul,add_zero,zero_add,hr,integral_zero_measure]

/-- The complete flight-coordinate estimate, including the case of zero
exceptional mass. Nontrivial slow mass is the only restriction on the split. -/
theorem A1.capped_corrector_flight_bound {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar:ℝ) (hcomp:μ (fastVelocitySet vstar)ᶜ≠0) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let pre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let final := cappedFlightLaw μ h vstar h
    let post := final.map (kickEquiv (gradient U) hg (h/2))
    a.corrector post-a.corrector pre ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy pre (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy post (stdGaussian E) 0).toReal)-
        (1/2:ℝ)*(klDiv μ.fst (positionGibbs U)).toReal)+
      h*((13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂μ)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂μ)+
        7*cappedMidEntropyError U μ D vstar)+
      2*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂μ)*
        QuadraticTransport.wassersteinTwo ⟨(transportJoint μ (h/2)).fst,inferInstance⟩ a.targetProbability := by
  by_cases hpos:μ (fastVelocitySet vstar)=0
  · have hr : μ.restrict (fastVelocitySet vstar)=0 := Measure.restrict_eq_zero.mpr hpos
    have hb := a.verlet_corrector_flight_coarse hsm μ hμ hK hh
    dsimp only
    simp only [cappedFlightLaw_eq_transport_of_fast_null μ h vstar h hpos,
      cappedMidEntropyError_of_fast_null U μ D vstar hpos,hr,integral_zero_measure,
      Real.sqrt_zero,mul_zero,zero_mul,add_zero]
    exact hb
  · exact a.capped_corrector_flight_coarse hsm hstar hzero hh hL μ hμ hK D hD hcap vstar hpos hcomp

end PersistencePays
#print axioms PersistencePays.A1.capped_corrector_flight_coarse
