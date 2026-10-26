import PersistencePays.MeanAccelerationDefect
import PersistencePays.GaussianMeanPDE
import PersistencePays.GaussianStressBounds
import PersistencePays.GaussianCompactBounds
import PersistencePays.CompactGaussianMoments

/-! The actual mean-flow upper rate for compact Gaussian regularization.
All covariance, density, material-acceleration, and integrability hypotheses
are proved for the actual joint law; the only target hypothesis is A1. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory QuadraticTransport
open scoped ENNReal RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem A1.gaussianFlight_mean_upper_rate {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure Z) [IsProbabilityMeasure μ] (g:Z→E×E) (hg:Continuous g)
    {ε:ℝ} (hε:0<ε) (s:ℝ) :
    letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
    (∫y,‖gaussianMeanField μ g ε s y‖^2 ∂(gaussianFlightLaw (μ.map g) ε s).fst)+
      (∫y,⟪materialAcceleration (gaussianMeanField μ g ε).uncurry (s,y),
        y-positionBrenierMap (gaussianFlightLaw (μ.map g) ε s) a.targetProbability y⟫
        ∂(gaussianFlightLaw (μ.map g) ε s).fst)≤
      6*(conditionalGaussianEntropy (gaussianFlightLaw (μ.map g) ε s)
        (stdGaussian E) 0).toReal-
      (boltzmannEntropy (gaussianFlightLaw (μ.map g) ε s).fst-
        boltzmannEntropy (positionGibbs U)) := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  obtain ⟨A,B,hA,hB⟩:=compact_regression_uniform_bounds g hg hε.ne'
  obtain ⟨C,hC,hbounds⟩:=gaussianFlightStress_bounds μ g hg hε A B hA hB
  have hn:Continuous (gaussianFlightDensity μ g ε s):=
    (gaussianFlightDensity_contDiff 1 μ g hg hε.ne').continuous.comp
      (continuous_const.prodMk continuous_id)
  have hv:∀ᵐ y ∂(gaussianFlightLaw (μ.map g) ε s).fst,
      gaussianMeanField μ g ε s y=conditionalMeanVelocity (gaussianFlightLaw (μ.map g) ε s) y :=
    (gaussianMeanField_eq_conditionalMean μ g hg hε s).mono (fun y hy=>hy.symm)
  exact a.mean_acceleration_upper_rate _
    (compactGaussianFlight_memLp μ g hg ε s 2 (by norm_num))
    (a.compactGaussianFlight_entropy_finite μ g hg ε s hε.ne').1
    hn (gaussianFlightDensity_pos μ g hg hε s)
    (gaussianFlightLaw_fst_density μ g hg hε s)
    (gaussianFlightStress_space_contDiff μ g hg hε s)
    (fun y=>(hbounds s y).1) (fun y=>(hbounds s y).2)
    (gaussianFlightStress_actual μ g hg hε s) hv
    (gaussianMean_material_identity μ g hg hε s)

/-- The literal rate hypothesis of the free-transport corrector theorem, for
Gaussian regularization of an arbitrary compact latent probability law. -/
theorem A1.gaussianSmoothed_mean_upper_rate {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure Z) [IsProbabilityMeasure μ] (g:Z→E×E) (hg:Continuous g)
    {ε:ℝ} (hε:0<ε) (s:ℝ) :
    letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
    (∫y,‖gaussianMeanField μ g ε s y‖^2
      ∂transportPosition (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) s)+
      (∫y,⟪materialAcceleration (gaussianMeanField μ g ε).uncurry (s,y),
        y-positionBrenierMap (transportJoint (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) s)
          a.targetProbability y⟫
        ∂transportPosition (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) s)≤
      6*(conditionalGaussianEntropy (fullGaussianOUKernel 1 ε ∘ₘ μ.map g)
        (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition (fullGaussianOUKernel 1 ε ∘ₘ μ.map g) s)-
        boltzmannEntropy (positionGibbs U)) := by
  letI : IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  have hh:=a.gaussianFlight_mean_upper_rate μ g hg hε s
  simpa only [gaussianFlightLaw_transport,conditionalGaussianEntropy,
    transportJoint_zero,transportPosition_zero,transportPosition] using hh

end PersistencePays
#print axioms PersistencePays.A1.gaussianFlight_mean_upper_rate
#print axioms PersistencePays.A1.gaussianSmoothed_mean_upper_rate
