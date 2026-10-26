import PersistencePays.GaussianSinglePDE

/-! Exact momentum conservation for a Gaussian-regularized flight component. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def singleFlightMoment (ε s:ℝ) (y:E) (z:E×E):E→L[ℝ]E :=
  singleFlightDensity ε s y z • rankOneField (fun y=>singleFlightVelocity s y z) y+
  singleFlightDensity ε s y z • ((ε^2/(1+s^2))•ContinuousLinearMap.id ℝ E)

lemma matrixDivergence_add {M S:E→E→L[ℝ]E} (hM:ContDiff ℝ 1 M)
    (hS:ContDiff ℝ 1 S) (y:E) :
    matrixDivergence (fun x=>M x+S x) y=matrixDivergence M y+matrixDivergence S y := by
  have hd:= (hM.differentiable one_ne_zero y).hasFDerivAt.add
    (hS.differentiable one_ne_zero y).hasFDerivAt
  change HasFDerivAt (fun x=>M x+S x) _ y at hd
  simp only [matrixDivergence,hd.fderiv,ContinuousLinearMap.add_apply,Finset.sum_add_distrib]

lemma matrixDivergence_const (M:E→L[ℝ]E) (y:E) : matrixDivergence (fun _=>M) y=0 := by
  simp [matrixDivergence]

lemma singleFlightMoment_space_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) (s:ℝ) (z:E×E) :
    ContDiff ℝ n (fun y=>singleFlightMoment ε s y z) := by
  have hn:=singleFlightDensity_space_contDiff n hε s z
  have hb:=singleFlightVelocity_space_contDiff n s z
  have hR:ContDiff ℝ n (rankOneField (fun y=>singleFlightVelocity s y z)) := by
    unfold rankOneField
    exact ((ContinuousLinearMap.smulRightL ℝ E E).contDiff.comp
      ((innerSL ℝ).contDiff.comp hb)).clm_apply hb
  exact (hn.smul hR).add (hn.smul contDiff_const)

lemma singleFlightMoment_divergence {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    matrixDivergence (fun y=>singleFlightMoment ε s y z) y=
      vectorDivergence (fun y=>singleFlightDensity ε s y z•singleFlightVelocity s y z) y •
        singleFlightVelocity s y z+
      singleFlightDensity ε s y z •
        fderiv ℝ (fun y=>singleFlightVelocity s y z) y (singleFlightVelocity s y z)+
      (ε^2/(1+s^2)) • gradient (fun y=>singleFlightDensity ε s y z) y := by
  have hn:=singleFlightDensity_space_contDiff 1 hε s z
  have hb:=singleFlightVelocity_space_contDiff 1 s z
  have hi:ContDiff ℝ 1 (fun _ : E=>(ε^2/(1+s^2))•ContinuousLinearMap.id ℝ E) := contDiff_const
  unfold singleFlightMoment
  have ha:=matrixDivergence_add (hn.smul (rankOneField_contDiff hb)) (hn.smul hi) y
  trans matrixDivergence (fun y=>singleFlightDensity ε s y z • rankOneField (fun y=>singleFlightVelocity s y z) y) y+
    matrixDivergence (fun y=>singleFlightDensity ε s y z • ((ε^2/(1+s^2))•ContinuousLinearMap.id ℝ E)) y
  · exact ha
  rw [matrixDivergence_weighted_rankOne hn hb,matrixDivergence_smul hn hi,matrixDivergence_const]
  simp

theorem singleFlight_momentum {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) (z:E×E) :
    deriv (fun t=>singleFlightDensity ε t y z•singleFlightVelocity t y z) s+
      matrixDivergence (fun y=>singleFlightMoment ε s y z) y=0 := by
  have hn:=singleFlightDensity_time hε s y z
  have hb:=singleFlightVelocity_time s y z
  have hd:=hn.smul hb
  change HasDerivAt (fun t=>singleFlightDensity ε t y z•singleFlightVelocity t y z) _ s at hd
  rw [hd.deriv,singleFlightMoment_divergence hε]
  have hc:=singleFlight_continuity hε s y z
  rw [hn.deriv] at hc
  have hm:=singleFlightVelocity_material s y z
  rw [hb.deriv] at hm
  have hg:=singleFlightDensity_gradient hε s y z
  have hs: (ε^2/(1+s^2))*(-(singleFlightDensity ε s y z/(ε^2*(1+s^2))))=
      -singleFlightDensity ε s y z*((1+s^2)^2)⁻¹ := by
    field_simp
    <;> ring
  rw [hg,smul_smul,hs]
  calc
    _ = (singleFlightDensity ε s y z *
        (-(↑(Module.finrank ℝ E)*regressionBeta s)+
        ⟪flightResidual s y z,singleFlightVelocity s y z⟫/(ε^2*(1+s^2)))+
        vectorDivergence (fun y=>singleFlightDensity ε s y z•singleFlightVelocity s y z) y) •
        singleFlightVelocity s y z+
      singleFlightDensity ε s y z •
        ((((1-s^2)/(1+s^2)^2)•flightResidual s y z-regressionBeta s•z.2)+
        fderiv ℝ (fun y=>singleFlightVelocity s y z) y (singleFlightVelocity s y z))+
      (-singleFlightDensity ε s y z*((1+s^2)^2)⁻¹) • flightResidual s y z := by module
    _ = 0 := by rw [hc,hm]; module

end PersistencePays
#print axioms PersistencePays.singleFlight_momentum
