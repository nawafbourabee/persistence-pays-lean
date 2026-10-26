import PersistencePays.GaussianSingleDensity

/-! Exact derivatives of one Gaussian observation density and its regression mean. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def singleFlightVelocity (s:ℝ) (y:E) (z:E×E):E :=
  z.2+regressionBeta s • flightResidual s y z

lemma singleFlightVelocity_eq (s:ℝ) (y:E) (z:E×E) :
    singleFlightVelocity s y z=regressionBeta s • y+regressionLatentMean s z := by
  rw [regressionLatentMean_identity]
  unfold singleFlightVelocity flightResidual
  module

lemma singleFlightLog_space {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    HasFDerivAt (fun y=>singleFlightLog ε s y z)
      (-((ε^2*(1+s^2))⁻¹) • innerSL ℝ (flightResidual s y z)) y := by
  have hd:1+s^2≠0 := by positivity
  have hr:HasFDerivAt (fun y:E=>flightResidual s y z) (ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).sub_const _
  have hh:=((hr.norm_sq).mul_const (2*ε^2*(1+s^2))⁻¹).const_sub
    (-((Module.finrank ℝ E:ℝ)/2)*Real.log (1+s^2))
  convert hh using 1 <;> try rfl
  ext v
  simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    innerSL_apply_apply]
  field_simp
  <;> ring

lemma singleFlightDensity_space {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    HasFDerivAt (fun y=>singleFlightDensity ε s y z)
      (-(singleFlightDensity ε s y z/(ε^2*(1+s^2))) •
        innerSL ℝ (flightResidual s y z)) y := by
  have hh:=((singleFlightLog_space hε s y z).exp).const_mul
    (heatConstant E 1*ε⁻¹^Module.finrank ℝ E)
  convert hh using 1 <;> try rfl
  ext v
  simp [singleFlightDensity,div_eq_mul_inv]
  <;> ring

lemma singleFlightLog_time {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    HasDerivAt (fun t=>singleFlightLog ε t y z)
      (-((Module.finrank ℝ E:ℝ)*regressionBeta s)+
        ⟪flightResidual s y z,singleFlightVelocity s y z⟫/(ε^2*(1+s^2))) s := by
  have hd:1+s^2≠0 := by positivity
  have hD:HasDerivAt (fun t:ℝ=>1+t^2) (2*s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add 1
  have hr:HasDerivAt (fun t=>flightResidual t y z) (-z.2) s := by
    simpa [flightResidual,latentCenter] using
      (((hasDerivAt_id s).smul_const z.2).const_add z.1).const_sub y
  have hh:=((hD.log hd).const_mul (-((Module.finrank ℝ E:ℝ)/2))).sub
    ((hr.norm_sq).div (hD.const_mul (2*ε^2)) (mul_ne_zero (by positivity) hd))
  convert hh using 1 <;> try rfl
  simp only [singleFlightVelocity,inner_add_right,real_inner_smul_right,
    inner_neg_right,real_inner_self_eq_norm_sq,regressionBeta]
  field_simp
  <;> ring

lemma singleFlightDensity_time {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    HasDerivAt (fun t=>singleFlightDensity ε t y z)
      (singleFlightDensity ε s y z *
        (-((Module.finrank ℝ E:ℝ)*regressionBeta s)+
        ⟪flightResidual s y z,singleFlightVelocity s y z⟫/(ε^2*(1+s^2)))) s := by
  convert ((singleFlightLog_time hε s y z).exp).const_mul
    (heatConstant E 1*ε⁻¹^Module.finrank ℝ E) using 1 <;> try rfl
  dsimp [singleFlightDensity]
  ring

lemma singleFlightVelocity_space (s:ℝ) (y:E) (z:E×E) :
    HasFDerivAt (fun y=>singleFlightVelocity s y z)
      (regressionBeta s • ContinuousLinearMap.id ℝ E) y := by
  exact (((hasFDerivAt_id y).sub_const _).const_smul _).const_add _

end PersistencePays
#print axioms PersistencePays.singleFlightLog_time
#print axioms PersistencePays.singleFlightDensity_time
#print axioms PersistencePays.singleFlightDensity_space
