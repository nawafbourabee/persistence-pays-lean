import PersistencePays.SmoothCharacteristicClosure
import PersistencePays.GaussianMeanUpperRate

/-! The smooth free-transport corrector inequality for every actual compact
latent Gaussian mixture. All density, flow, covariance, and entropy inputs
are derived from the actual law and the target assumption A1. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem A1.compactGaussian_freeTransport {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure Z) [IsProbabilityMeasure μ] (g:Z→E×E) (hg:Continuous g)
    {ε T:ℝ} (hε:0<ε) (hT:0<T) :
    letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
    a.corrector (transportJoint (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) T)-
      a.corrector (fullGaussianOUKernel 1 ε ∘ₘ μ.map g)≤
      freeTransportRHS (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) (positionGibbs U) T := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  let ρ:Measure (E×E):=fullGaussianOUKernel 1 ε ∘ₘ μ.map g
  have hρ8:MemLp id 8 ρ:=compactGaussianSmoothing_memLp μ g hg ε 8 (by norm_num)
  have hρ2:MemLp id 2 ρ:=hρ8.mono_exponent (by norm_num)
  have hK:klDiv ρ (phaseGibbs U)≠∞:=a.gaussianSmoothing_gibbs_entropy_finite _
    (compactLatent_memLp μ g hg) 1 ε hε.ne'
  have hac:ρ≪(volume:Measure E).prod volume:=
    (fullGaussianOUKernel_density_cap (μ.map g) 1 ε hε.ne').absolutelyContinuous.trans
      ((Measure.AbsolutelyContinuous.refl ((volume:Measure E).prod volume)).smul_left _)
  obtain ⟨A,B,hA,hB⟩:=compact_regression_uniform_bounds g hg hε.ne'
  obtain ⟨C,hC,hGrowth⟩:=gaussianMeanField_joint_growth μ g hg hε.ne' 0 T
  let δ0:=1/(2*(1+2*(A:ℝ)*B))
  have hδ0:0<δ0:=by dsimp [δ0]; positivity
  have hField:ContDiff ℝ 2 (gaussianMeanField μ g ε).uncurry:=
    gaussianMeanField_contDiff 2 μ g hg hε.ne'
  have hDensity:∀s∈Icc 0 T,transportPosition ρ s=
      volume.withDensity (fun x=>ENNReal.ofReal (gaussianFlightDensity μ g ε s x)):=by
    intro s _
    rw [transportPosition,show transportJoint ρ s=gaussianFlightLaw (μ.map g) ε s from
      (gaussianFlightLaw_transport (μ.map g) ε s).symm]
    exact gaussianFlightLaw_fst_density μ g hg hε s
  apply a.free_transport_of_smooth_characteristics ρ hρ8 hK hac hT hδ0 hC
    (gaussianMeanField μ g ε).uncurry hField (gaussianFlightDensity μ g ε).uncurry
    hDensity
  · intro s _ x
    exact (gaussianFlightDensity_contDiff 1 μ g hg hε.ne').differentiable one_ne_zero (s,x)
  · intro s _ x
    exact gaussianFlightDensity_pos μ g hg hε s x
  · intro s _ x
    exact gaussianFlight_characteristic_PDE μ g hg hε s x
  · exact hGrowth
  · intro s _
    have hh:=gaussianMeanField_eq_conditionalMean μ g hg hε s
    have he:gaussianFlightLaw (μ.map g) ε s=transportJoint ρ s:=
      gaussianFlightLaw_transport (μ.map g) ε s
    simp only [he] at hh
    exact hh.mono (fun x hx=>hx.symm)
  · intro s _
    exact a.gaussianSmoothed_mean_upper_rate μ g hg hε s
  · intro s hs t ht hst
    apply gaussianMeanField_variational_flow μ g hg hε.ne' A B hA hB min_le_max
    have hden:0<2*(1+2*(A:ℝ)*B):=by positivity
    have hh:2*(1+2*(A:ℝ)*B)*|t-s|≤1:=by
      exact (mul_le_mul_of_nonneg_left hst hden.le).trans_eq (by dsimp [δ0]; field_simp)
    rw [max_sub_min_eq_abs]
    exact hh

end PersistencePays
#print axioms PersistencePays.A1.compactGaussian_freeTransport
