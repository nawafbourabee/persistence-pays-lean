import PersistencePays.GaussianStressIdentity
import PersistencePays.MeanFlowMaterial

/-! The true material acceleration of the actual Gaussian conditional mean is
exactly minus the covariance-stress divergence divided by the density. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem gaussianMean_material_identity (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    gaussianFlightDensity μ g ε s y •
      materialAcceleration (gaussianMeanField μ g ε).uncurry (s,y)=
      -matrixDivergence (gaussianFlightStress μ g ε s) y := by
  have hnJ:=gaussianFlightDensity_contDiff 1 μ g hg hε.ne'
  have hbJ:=gaussianMeanField_contDiff 1 μ g hg hε.ne'
  have hp:ContDiff ℝ 1 (fun y:E=>(s,y)):=contDiff_const.prodMk contDiff_id
  have ht:ContDiff ℝ 1 (fun t:ℝ=>(t,y)):=contDiff_id.prodMk contDiff_const
  have hn:ContDiff ℝ 1 (gaussianFlightDensity μ g ε s):=hnJ.comp hp
  have hb:ContDiff ℝ 1 (gaussianMeanField μ g ε s):=hbJ.comp hp
  have hM := (gaussianFlightSecondMoment_contDiff 1 μ g hg hε.ne').comp hp
  have hnT:HasDerivAt (fun t=>gaussianFlightDensity μ g ε t y)
      (deriv (fun t=>gaussianFlightDensity μ g ε t y) s) s :=
    ((hnJ.comp ht).differentiable one_ne_zero s).hasDerivAt
  have hbT:HasDerivAt (fun t=>gaussianMeanField μ g ε t y)
      (deriv (fun t=>gaussianMeanField μ g ε t y) s) s :=
    ((hbJ.comp ht).differentiable one_ne_zero s).hasDerivAt
  have hJ:gaussianFlightFlux μ g ε=(fun t y=>gaussianFlightDensity μ g ε t y•gaussianMeanField μ g ε t y) := by
    funext t y
    exact gaussianFlightFlux_eq_density_mean μ g hg hε t y
  have hc:=gaussianFlight_continuity μ g hg hε.ne' s y
  have hm:=gaussianFlight_momentum μ g hg hε.ne' s y
  rw [hJ] at hc hm
  have hmat:=material_derivative_from_moment_PDE hn hb hM hnT hbT hc hm
  have he:(fun y=>gaussianFlightSecondMoment μ g ε s y-
      gaussianFlightDensity μ g ε s y•rankOneField (gaussianMeanField μ g ε s) y)=
      gaussianFlightStress μ g ε s := by
    funext y
    exact (gaussianFlightStress_eq_moment_defect μ g hg hε s y).symm
  dsimp only [Function.comp_def,Function.uncurry_apply_pair] at hmat
  rw [he] at hmat
  rw [materialAcceleration_eq_time_spatial (hbJ.differentiable one_ne_zero)]
  exact hmat

/-- The literal characteristic equation for the actual position density. -/
theorem gaussianFlight_characteristic_PDE (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    fderiv ℝ (gaussianFlightDensity μ g ε).uncurry (s,y)
      (1,gaussianMeanField μ g ε s y)=
    -gaussianFlightDensity μ g ε s y *
      (fderiv ℝ (gaussianMeanField μ g ε s) y).toLinearMap.trace ℝ E := by
  have hnJ:=gaussianFlightDensity_contDiff 1 μ g hg hε.ne'
  have hbJ:=gaussianMeanField_contDiff 1 μ g hg hε.ne'
  have hp:ContDiff ℝ 1 (fun y:E=>(s,y)):=contDiff_const.prodMk contDiff_id
  have hn:ContDiff ℝ 1 (gaussianFlightDensity μ g ε s):=hnJ.comp hp
  have hb:ContDiff ℝ 1 (gaussianMeanField μ g ε s):=hbJ.comp hp
  have hd:DifferentiableAt ℝ (gaussianFlightDensity μ g ε).uncurry (s,y):=
    hnJ.differentiable one_ne_zero (s,y)
  have ht:HasDerivAt (fun t=>gaussianFlightDensity μ g ε t y)
      (fderiv ℝ (gaussianFlightDensity μ g ε).uncurry (s,y) (1,0)) s:=
    by
      have hh := hd.hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
      simpa only [Function.comp_def,Function.uncurry_apply_pair,id_eq] using hh
  have hx:HasFDerivAt (gaussianFlightDensity μ g ε s)
      ((fderiv ℝ (gaussianFlightDensity μ g ε).uncurry (s,y)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)) y:=
    hd.hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜:=ℝ) s y).prodMk (hasFDerivAt_id y))
  have hJ:gaussianFlightFlux μ g ε=(fun t y=>gaussianFlightDensity μ g ε t y•gaussianMeanField μ g ε t y) := by
    funext t y
    exact gaussianFlightFlux_eq_density_mean μ g hg hε t y
  have hc:=gaussianFlight_continuity μ g hg hε.ne' s y
  rw [hJ,vectorDivergence_smul hn hb,vectorDivergence_eq_trace,
    ht.deriv,hx.fderiv,ContinuousLinearMap.comp_apply] at hc
  have hs:((1:ℝ),gaussianMeanField μ g ε s y)=
      (1,0)+(0,gaussianMeanField μ g ε s y):=by ext <;> simp
  rw [hs,map_add]
  simp only [ContinuousLinearMap.inr_apply] at hc
  linarith

end PersistencePays
#print axioms PersistencePays.gaussianMean_material_identity

#print axioms PersistencePays.gaussianFlight_characteristic_PDE
