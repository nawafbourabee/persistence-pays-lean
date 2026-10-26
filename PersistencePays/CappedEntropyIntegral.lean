import PersistencePays.CappedEnergy
import PersistencePays.CappedCorrectorFlight

/-! The actual time-integrated velocity entropy along a capped flight. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cappedMidEntropyError (U:E→ℝ) (μ:Measure (E×E)) (D vstar:ℝ) : ℝ :=
  let α := (μ (fastVelocitySet vstar)).toReal
  3*α*Real.log (1/α)+2*α+α*max (Real.log D) 0+
    α*(Module.finrank ℝ E:ℝ)*Real.log (2*Real.pi)+
    ∫z in fastVelocitySet vstar,(2*U z.1+‖z.2‖^2)∂μ

theorem cappedFlight_entropy_first (μ:Measure (E×E)) {h vstar s:ℝ} (hs:s ≤ h/2) :
    conditionalGaussianEntropy (cappedFlightLaw μ h vstar s) (stdGaussian E) 0=
      conditionalGaussianEntropy μ (stdGaussian E) s := by
  rw [cappedFlightLaw_first μ hs]
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition]

theorem cappedFlight_entropy_second (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {h vstar s:ℝ} (hs:0 ≤ s) :
    conditionalGaussianEntropy (cappedFlightLaw μ h vstar (s+h/2)) (stdGaussian E) 0=
      conditionalGaussianEntropy (cappedMidpointLaw μ h vstar) (stdGaussian E) s := by
  rcases eq_or_lt_of_le hs with he|he
  · subst s
    rw [zero_add,cappedFlight_entropy_first μ le_rfl]
    unfold cappedMidpointLaw
    rw [speedFlip_conditional_entropy]
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition]
  · rw [cappedFlightLaw_second μ (by linarith : h/2<s+h/2),add_sub_cancel_right]
    simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero,transportPosition]
    rfl

theorem A1.cappedFlight_entropy_bound {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar s:ℝ) (hs:0 ≤ s) (hsh:s ≤ h)
    (hpos:μ (fastVelocitySet vstar)≠0) (hcomp:μ (fastVelocitySet vstar)ᶜ≠0) :
    (conditionalGaussianEntropy (cappedFlightLaw μ h vstar s) (stdGaussian E) 0).toReal ≤
      (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
      (conditionalGaussianEntropy (cappedFlightLaw μ h vstar h) (stdGaussian E) 0).toReal+
      cappedMidEntropyError U μ D vstar := by
  have hno := a.cappedFlight_entropy_no_overshoot μ hμ hK hh hs hsh hpos hcomp
  have he := a.cappedFlight_exceptional_entropy hstar hzero hh.le hL μ hμ hK D hD hcap vstar s hs hsh hpos
  let α := (μ (fastVelocitySet vstar)).toReal
  have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
  have hα1 : α≤1 := measureReal_le_one
  have hb := binaryEntropy_le hα0 hα1
  dsimp only at hno he
  unfold cappedMidEntropyError
  dsimp only
  dsimp only [α] at hb
  nlinarith

theorem A1.cappedEntropyIntegral_bound {U:E→ℝ} {L h:ℝ} (a:A1 U 1 L)
    (hstar:a.minimizer=0) (hzero:U 0=0) (hh:0 < h) (hL:L*h^2≤1/2)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (D:ℝ) (hD:0 < D)
    (hcap:μ≤ENNReal.ofReal D • ((volume:Measure E).prod volume))
    (vstar:ℝ) (hpos:μ (fastVelocitySet vstar)≠0) (hcomp:μ (fastVelocitySet vstar)ᶜ≠0) :
    cappedEntropyIntegral μ h vstar ≤
      h*((conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
        (conditionalGaussianEntropy (cappedFlightLaw μ h vstar h) (stdGaussian E) 0).toReal)+
      h*cappedMidEntropyError U μ D vstar := by
  let plus := cappedMidpointLaw μ h vstar
  let C := (conditionalGaussianEntropy μ (stdGaussian E) 0).toReal+
    (conditionalGaussianEntropy (cappedFlightLaw μ h vstar h) (stdGaussian E) 0).toReal+
      cappedMidEntropyError U μ D vstar
  have hp := cappedMidpointLaw_memLp μ hμ h vstar
  have hpk := a.cappedMidpoint_entropy_finite μ hμ hK h vstar
  have hi0 := (a.lemma_4_9_i μ (by linarith : 0<h/2) hμ hK).2.1
  have hi1 := (a.lemma_4_9_i plus (by linarith : 0<h/2) hp hpk).2.1
  have hfirst := intervalIntegral.integral_mono_on (by linarith : (0:ℝ)≤h/2) hi0
    (intervalIntegrable_const (c:=C)) (fun s hs=>by
      have hb := a.cappedFlight_entropy_bound hstar hzero hh hL μ hμ hK D hD hcap vstar s
        hs.1 (by linarith [hs.2]) hpos hcomp
      rwa [cappedFlight_entropy_first μ hs.2] at hb)
  have hsecond := intervalIntegral.integral_mono_on (by linarith : (0:ℝ)≤h/2) hi1
    (intervalIntegrable_const (c:=C)) (fun s hs=>by
      have hb := a.cappedFlight_entropy_bound hstar hzero hh hL μ hμ hK D hD hcap vstar (s+h/2)
        (by linarith [hs.1]) (by linarith [hs.2]) hpos hcomp
      rwa [cappedFlight_entropy_second μ hs.1] at hb)
  rw [intervalIntegral.integral_const] at hfirst hsecond
  simp only [sub_zero,smul_eq_mul] at hfirst hsecond
  unfold cappedEntropyIntegral
  dsimp only [C,plus] at hfirst hsecond
  linarith

end PersistencePays
#print axioms PersistencePays.A1.cappedEntropyIntegral_bound
