import PersistencePays.CappedCorrectorCoarse

/-! Proposition 5.9 for the literal comparison Verlet map. Its only analytic
premise still pending is the explicit smooth free-flight theorem. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance comparisonVerlet_map_probability (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (g:E→E) (hg:Measurable g) (h vstar:ℝ) :
    IsProbabilityMeasure (μ.map (comparisonVerletEquiv g hg h vstar)) :=
  Measure.isProbabilityMeasure_map (comparisonVerletEquiv g hg h vstar).measurable.aemeasurable

def A1.comparisonCorrectorError {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (h D vstar:ℝ) : ℝ :=
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let q := μ.map (kickEquiv (gradient U) hg (h/2))
  (13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂q)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂q)+
    (2/h)*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂q)*
      QuadraticTransport.wassersteinTwo ⟨(transportJoint q (h/2)).fst,inferInstance⟩ a.targetProbability+
    7*cappedMidEntropyError U q D vstar

/-- The comparison-stage corrector inequality is valid for every exceptional
mass strictly below one; the manuscript's `α ≤ exp(-1)` is a stronger restriction.
The density cap and all endpoint laws are the actual ones. -/
theorem A1.proposition_5_9 {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hsm:GaussianSmoothedFreeTransportBound a)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar:ℝ) (hα:(μ {z|vstar<‖flightVelocity (gradient U) h z‖}).toReal<1) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let post := μ.map (comparisonVerletEquiv (gradient U) hg h vstar)
    a.corrector post-a.corrector μ ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy post (stdGaussian E) 0).toReal)-
        (1/2:ℝ)*(klDiv μ.fst (positionGibbs U)).toReal)+h*a.comparisonCorrectorError μ h D vstar := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let ek := kickEquiv (gradient U) hg (h/2)
  let q := μ.map ek
  letI : IsProbabilityMeasure q := Measure.isProbabilityMeasure_map ek.measurable.aemeasurable
  have hq : MemLp id 2 q :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable ek.measurable.aemeasurable).mpr
      (a.kick_memLp hμ (h/2))
  have hqK : klDiv q (phaseGibbs U)≠∞ :=
    a.volume_stage_entropy_finite μ ek (kick_measurePreserving (gradient U) hg (h/2))
      hμ (a.kick_memLp hμ (h/2)) hK
  have hqcap := volume_stage_density_cap μ (ENNReal.ofReal D) hcap ek
    (kick_measurePreserving (gradient U) hg (h/2))
  have hmass : q (fastVelocitySet vstar)=μ {z|vstar<‖flightVelocity (gradient U) h z‖} := by
    rw [show q=μ.map ek from rfl,Measure.map_apply ek.measurable (fastVelocitySet_measurable vstar)]
    rfl
  have hcomp : q (fastVelocitySet vstar)ᶜ≠0 := by
    intro hz
    have hc := probability_complement_toReal q (fastVelocitySet vstar) (fastVelocitySet_measurable vstar)
    rw [hz,ENNReal.toReal_zero,hmass] at hc
    linarith
  have hpre : q.map (kickEquiv (gradient U) hg (-h/2))=μ := by
    rw [show q=μ.map ek from rfl,Measure.map_map (kickEquiv (gradient U) hg (-h/2)).measurable ek.measurable]
    have he : (kickEquiv (gradient U) hg (-h/2)) ∘ ek=id := by
      funext z
      change kick (gradient U) (-h/2) (kick (gradient U) (h/2) z)=z
      simpa only [neg_div] using kick_inverse (gradient U) (h/2) z
    rw [he,Measure.map_id]
  have hpost : (cappedFlightLaw q h vstar h).map ek=
      μ.map (comparisonVerletEquiv (gradient U) hg h vstar) := by
    unfold cappedFlightLaw
    rw [show q=μ.map ek from rfl,Measure.map_map (cappedFlightEquiv h vstar h).measurable ek.measurable,
      Measure.map_map ek.measurable ((cappedFlightEquiv h vstar h).measurable.comp ek.measurable)]
    congr 1
    funext z
    change kick (gradient U) (h/2) (cappedFlightEquiv h vstar h (kick (gradient U) (h/2) z))=
      comparisonVerlet (gradient U) h vstar z
    rw [comparisonVerlet_factorization]
    simp only [cappedFlightEquiv,show ¬h≤h/2 by linarith,ite_false,MeasurableEquiv.trans_apply,
      show h-h/2=h/2 by ring]
    rfl
  have hpost' : (cappedFlightLaw q h vstar h).map (kickEquiv (gradient U) hg (h/2))=
      μ.map (comparisonVerletEquiv (gradient U) hg h vstar) := hpost
  have hfst : q.fst=μ.fst := map_position_preserving_fst μ ek (fun _=>rfl)
  have hb := a.capped_corrector_flight_bound hsm hstar hzero hh hL q hq hqK D hD hqcap vstar hcomp
  dsimp only at hb ⊢
  simp only [hpre,hpost',hfst] at hb
  dsimp only [A1.comparisonCorrectorError]
  have hcancel : h*(2/h)=2 := by field_simp [hh.ne']
  change a.corrector (μ.map (comparisonVerletEquiv (gradient U) hg h vstar))-a.corrector μ≤_ at hb ⊢
  change _≤h*((13/2:ℝ)*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
    (conditionalGaussianEntropy (μ.map (comparisonVerletEquiv (gradient U) hg h vstar)) (stdGaussian E) 0).toReal)-
      (1/2:ℝ)*(klDiv μ.fst (positionGibbs U)).toReal)+
    h*((13/4:ℝ)*L*h^2*(∫z,‖z.2‖^2∂q)+(13/2:ℝ)*(∫z in fastVelocitySet vstar,‖z.2‖^2∂q)+
      (2/h)*Real.sqrt (∫z in fastVelocitySet vstar,‖z.2‖^2∂q)*
      QuadraticTransport.wassersteinTwo ⟨(transportJoint q (h/2)).fst,inferInstance⟩ a.targetProbability+
      7*cappedMidEntropyError U q D vstar)
  convert hb using 1 <;> field_simp [hh.ne'] <;> ring

end PersistencePays
#print axioms PersistencePays.A1.proposition_5_9
