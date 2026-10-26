import PersistencePays.FreeTransportLimit
import PersistencePays.KickBalance

/-! The two force kicks and the actual free-flight inequality combine into
Propositions 4.10 and 4.11. The smooth free-flight theorem remains explicitly
parameterized until its independent analytic construction is complete. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.verlet_corrector_flight_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) {h : ℝ} (hh : 0 < h) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μpre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let μf := transportJoint μ h
    let μpost := μf.map (kickEquiv (gradient U) hg (h/2))
    a.corrector μpost-a.corrector μpre ≤
      6*(∫ s in (0:ℝ)..h, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal)-
        h/2*((klDiv μ.fst (positionGibbs U)).toReal+(klDiv μf.fst (positionGibbs U)).toReal)-
        h/2*(a.transportGap μ+a.transportGap μf)+entropyTrapezoidDefect μ h := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let μf := transportJoint μ h
  have hf : MemLp id 2 μf := transportProbability_memLp μ hμ h
  have hKf : klDiv μf (phaseGibbs U) ≠ ∞ :=
    a.volume_stage_entropy_finite μ (freeTransportEquiv h) (drift_measurePreserving h)
      hμ (drift_memLp hμ h) hK
  have hk0 := a.lemma_4_3 μ hμ hK (-h/2)
  have hk1 := a.lemma_4_3 μf hf hKf (h/2)
  have hflight := a.free_transport_of_smoothed_bound hsm (⟨μ,inferInstance⟩ : ProbabilityMeasure (E×E)) hμ hK hh
  have ht := (a.lemma_4_9_i μ hh hμ hK).2.2.1
  have he := (a.free_transport_entropy_balance μ hμ hK h).2.2
  dsimp only at hk0 hk1 ⊢
  change a.corrector (μf.map (kickEquiv (gradient U) hg (h/2)))-
    a.corrector (μ.map (kickEquiv (gradient U) hg (-h/2))) ≤ _
  change a.corrector μf-a.corrector μ ≤ _ at hflight
  change boltzmannEntropy μf.fst + _ = _ at he
  unfold freeTransportRHS at hflight
  change a.corrector (μ.map (kickEquiv (gradient U) hg (-h/2))) = _ at hk0
  change a.corrector (μf.map (kickEquiv (gradient U) hg (h/2))) = _ at hk1
  have heh := congrArg (fun x : ℝ => h*x) he
  dsimp only [μf] at hk0 hk1 heh hflight
  change a.corrector (transportJoint μ h)-a.corrector μ ≤
    7*(∫ s in (0:ℝ)..h, (conditionalGaussianEntropy μ (stdGaussian E) s).toReal)-
      h*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
      h*(boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) at hflight
  nlinarith

/-- Proposition 4.11 in the actual flight-law parametrization. The pre-law is
obtained by the inverse first kick, so this parametrization loses no inputs. -/
theorem A1.verlet_corrector_flight_coarse {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) {h : ℝ} (hh : 0 < h) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let μpre := μ.map (kickEquiv (gradient U) hg (-h/2))
    let μf := transportJoint μ h
    let μpost := μf.map (kickEquiv (gradient U) hg (h/2))
    a.corrector μpost-a.corrector μpre ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy μpre (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy μpost (stdGaussian E) 0).toReal)-
        1/2*(klDiv μ.fst (positionGibbs U)).toReal)+
        h*((13/4:ℝ)*L*h^2*(∫ z,‖z.2‖^2 ∂μ)) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let μf := transportJoint μ h
  have hf : MemLp id 2 μf := transportProbability_memLp μ hμ h
  have hKf : klDiv μf (phaseGibbs U) ≠ ∞ :=
    a.volume_stage_entropy_finite μ (freeTransportEquiv h) (drift_measurePreserving h)
      hμ (drift_memLp hμ h) hK
  have hb := a.verlet_corrector_flight_bound hsm μ hμ hK hh
  have ht := (a.lemma_4_9_i μ hh hμ hK).2.2.1
  have h0 := (a.free_transport_entropy_balance μ hμ hK 0).1
  have h1 := (a.free_transport_entropy_balance μ hμ hK h).1
  have hi := conditionalGaussianEntropy_intervalIntegrable μ hh h0 h1
  have hind := intervalIntegral.integral_mono_on hh.le hi
    (intervalIntegrable_const (c := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
      (conditionalGaussianEntropy μ (stdGaussian E) h).toReal)) (fun s hs => by
      have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h0,h1⟩)
        (corollary_3_5 μ hh hs.1 hs.2)
      rwa [ENNReal.toReal_add h0 h1] at hb)
  rw [intervalIntegral.integral_const] at hind
  simp only [sub_zero,smul_eq_mul] at hind
  have hgap0 := (a.transportGap_identity μ hμ hK).2.1
  have hgap1 := (a.transportGap_identity μf hf hKf).2.1
  have hbalance := (a.lemma_4_9_ii μ h hh.le hμ hK).2.2
  have hE : 0 ≤ (klDiv μf.fst (positionGibbs U)).toReal := ENNReal.toReal_nonneg
  dsimp only at hb hbalance ⊢
  have hEvf : conditionalGaussianEntropy μf (stdGaussian E) 0 =
      conditionalGaussianEntropy μ (stdGaussian E) h := by
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
    rfl
  change _ - ((conditionalGaussianEntropy ((μf.map (kickEquiv (gradient U) hg (h/2)))) (stdGaussian E) 0).toReal-
      (conditionalGaussianEntropy μf (stdGaussian E) 0).toReal) ≤ _ at hbalance
  rw [hEvf] at hbalance
  nlinarith [mul_nonneg hh.le hgap0,mul_nonneg hh.le hgap1,mul_nonneg hh.le hE]


theorem A1.verlet_corrector_bound {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (hsm : GaussianSmoothedFreeTransportBound a)
    (μ : Measure (E×E)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) {h : ℝ} (hh : 0 < h) :
    letI : IsProbabilityMeasure (μ.map (verlet (gradient U) h)) :=
      Measure.isProbabilityMeasure_map (verlet_measurePreserving (gradient U)
        (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h).measurable.aemeasurable
    a.corrector (μ.map (verlet (gradient U) h))-a.corrector μ ≤
      h*((13/2:ℝ)*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy (μ.map (verlet (gradient U) h)) (stdGaussian E) 0).toReal)-
        1/2*(klDiv μ.fst (positionGibbs U)).toReal)+
        h*((13/4:ℝ)*L*h^2*(∫ z,‖flightVelocity (gradient U) h z‖^2 ∂μ)) := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  letI : IsProbabilityMeasure (μ.map (verlet (gradient U) h)) :=
    Measure.isProbabilityMeasure_map (verlet_measurePreserving (gradient U) hg h).measurable.aemeasurable
  let ek := kickEquiv (gradient U) hg (h/2)
  let μ0 := μ.map ek
  letI : IsProbabilityMeasure μ0 := Measure.isProbabilityMeasure_map ek.measurable.aemeasurable
  have h0 : MemLp id 2 μ0 :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable ek.measurable.aemeasurable).mpr
      (a.kick_memLp hμ (h/2))
  have hK0 : klDiv μ0 (phaseGibbs U) ≠ ∞ :=
    a.volume_stage_entropy_finite μ ek (kick_measurePreserving (gradient U) hg (h/2))
      hμ (a.kick_memLp hμ (h/2)) hK
  have hpre : μ0.map (kickEquiv (gradient U) hg (-h/2)) = μ := by
    rw [show μ0=μ.map ek from rfl,Measure.map_map
      (kickEquiv (gradient U) hg (-h/2)).measurable ek.measurable]
    have he : (kickEquiv (gradient U) hg (-h/2)) ∘ ek = id := by
      funext z
      change kick (gradient U) (-h/2) (kick (gradient U) (h/2) z)=z
      simpa only [neg_div] using kick_inverse (gradient U) (h/2) z
    rw [he,Measure.map_id]
  have hpost : (transportJoint μ0 h).map (kickEquiv (gradient U) hg (h/2)) =
      μ.map (verlet (gradient U) h) := by
    change ((μ.map ek).map (freeTransport h)).map ek = _
    rw [Measure.map_map (measurable_freeTransport h) ek.measurable,
      Measure.map_map ek.measurable ((measurable_freeTransport h).comp ek.measurable)]
    rfl
  have hfst : μ0.fst=μ.fst := map_position_preserving_fst μ ek (fun _ => rfl)
  have hI : (∫ z,‖z.2‖^2 ∂μ0) = ∫ z,‖flightVelocity (gradient U) h z‖^2 ∂μ :=
    integral_map ek.measurable.aemeasurable (by fun_prop)
  have hb := a.verlet_corrector_flight_coarse hsm μ0 h0 hK0 hh
  dsimp only at hb
  simpa only [hpre,hpost,hfst,hI] using hb

end PersistencePays
#print axioms PersistencePays.A1.verlet_corrector_flight_coarse

#print axioms PersistencePays.A1.verlet_corrector_bound
