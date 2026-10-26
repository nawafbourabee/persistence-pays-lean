import PersistencePays.GaussianSingleDerivative
import PersistencePays.RankOneDivergence

/-! Classical continuity and momentum equations for each Gaussian flight component. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma singleFlightDensity_space_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) (s:ℝ) (z:E×E) :
    ContDiff ℝ n (fun y=>singleFlightDensity ε s y z) :=
  (singleFlightDensity_contDiff n hε).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)

lemma singleFlightVelocity_contDiff (n:ℕ) :
    ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>singleFlightVelocity p.1.1 p.1.2 p.2) := by
  unfold singleFlightVelocity regressionBeta flightResidual latentCenter
  exact contDiff_snd.snd.add ((contDiff_fst.fst.div
    (contDiff_const.add (contDiff_fst.fst.pow 2)) (fun p=>by positivity)).smul
    (contDiff_fst.snd.sub (contDiff_snd.fst.add (contDiff_fst.fst.smul contDiff_snd.snd))))

lemma singleFlightVelocity_space_contDiff (n:ℕ) (s:ℝ) (z:E×E) :
    ContDiff ℝ n (fun y=>singleFlightVelocity s y z) :=
  (singleFlightVelocity_contDiff n).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)

lemma singleFlightVelocity_time (s:ℝ) (y:E) (z:E×E) :
    HasDerivAt (fun t=>singleFlightVelocity t y z)
      (((1-s^2)/(1+s^2)^2)•flightResidual s y z-regressionBeta s •z.2) s := by
  have hd:1+s^2≠0 := by positivity
  have hD:HasDerivAt (fun t:ℝ=>1+t^2) (2*s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add 1
  have hβ:HasDerivAt regressionBeta ((1-s^2)/(1+s^2)^2) s := by
    convert (hasDerivAt_id s).div hD hd using 1 <;> try rfl
    simp only [id_eq]
    field_simp
    ring
  have hr:HasDerivAt (fun t=>flightResidual t y z) (-z.2) s := by
    simpa [flightResidual,latentCenter] using
      (((hasDerivAt_id s).smul_const z.2).const_add z.1).const_sub y
  convert (hβ.smul hr).const_add z.2 using 1 <;> try rfl
  module

lemma singleFlightVelocity_material (s:ℝ) (y:E) (z:E×E) :
    deriv (fun t=>singleFlightVelocity t y z) s +
      fderiv ℝ (fun y=>singleFlightVelocity s y z) y (singleFlightVelocity s y z)=
      ((1+s^2)^2)⁻¹•flightResidual s y z := by
  rw [(singleFlightVelocity_time s y z).deriv,(singleFlightVelocity_space s y z).fderiv]
  have hc:(1-s^2)/(1+s^2)^2+regressionBeta s*regressionBeta s=((1+s^2)^2)⁻¹ := by
    unfold regressionBeta
    field_simp
    <;> ring
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply]
  unfold singleFlightVelocity
  calc
    _ = (((1-s^2)/(1+s^2)^2)+regressionBeta s*regressionBeta s)•flightResidual s y z := by module
    _ = _ := by rw [hc]

lemma singleFlightVelocity_divergence (s:ℝ) (y:E) (z:E×E) :
    vectorDivergence (fun y=>singleFlightVelocity s y z) y=
      (Module.finrank ℝ E:ℝ)*regressionBeta s := by
  rw [vectorDivergence_eq_trace,(singleFlightVelocity_space s y z).fderiv]
  simp [mul_comm]

theorem singleFlight_continuity {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    deriv (fun t=>singleFlightDensity ε t y z) s+
      vectorDivergence (fun y=>singleFlightDensity ε s y z•singleFlightVelocity s y z) y=0 := by
  rw [(singleFlightDensity_time hε s y z).deriv,
    vectorDivergence_smul (singleFlightDensity_space_contDiff 1 hε s z)
      (singleFlightVelocity_space_contDiff 1 s z),singleFlightVelocity_divergence,
    (singleFlightDensity_space hε s y z).fderiv]
  simp only [ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma singleFlightDensity_gradient {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    gradient (fun y=>singleFlightDensity ε s y z) y=
      -(singleFlightDensity ε s y z/(ε^2*(1+s^2)))•flightResidual s y z := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,(singleFlightDensity_space hε s y z).fderiv]
  simp [real_inner_smul_left]

end PersistencePays
#print axioms PersistencePays.singleFlight_continuity
#print axioms PersistencePays.singleFlightVelocity_material
