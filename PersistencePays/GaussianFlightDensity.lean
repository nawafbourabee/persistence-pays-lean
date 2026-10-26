import PersistencePays.GaussianSingleDensity
import PersistencePays.GaussianMeanIdentification
import PersistencePays.TransportDensity

/-! The actual smooth positive position density of the compact Gaussian flight mixture. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def gaussianFlightDensity (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):ℝ :=
  ∫ z,singleFlightDensity ε s y (g z) ∂μ

lemma singleFlightDensity_latent_integrable (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    Integrable (fun z=>singleFlightDensity ε s y (g z)) μ := by
  have hS:Continuous (fun p:(ℝ×E)×(E×E)=>singleFlightDensity ε p.1.1 p.1.2 p.2) :=
    (singleFlightDensity_contDiff 0 hε).continuous
  have hc:Continuous (fun z:Z=>((s,y),g z)) := continuous_const.prodMk hg
  exact (hS.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem gaussianFlightDensity_contDiff (n:ℕ) (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (gaussianFlightDensity μ g ε).uncurry :=
  compact_mixture_integral_contDiff_real n μ g hg _ (singleFlightDensity_contDiff n hε)

lemma gaussianFlightDensity_pos (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) (y:E) :
    0<gaussianFlightDensity μ g ε s y := by
  apply (integral_pos_iff_support_of_nonneg (fun z=>(singleFlightDensity_pos hε s y (g z)).le)
    (singleFlightDensity_latent_integrable μ g hg hε.ne' s y)).mpr
  have he:Function.support (fun z=>singleFlightDensity ε s y (g z))=Set.univ := by
    ext z
    simp [Function.mem_support,(singleFlightDensity_pos hε s y (g z)).ne']
  rw [he,measure_univ]
  norm_num

theorem gaussianFlightLaw_fst_density (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    (gaussianFlightLaw (μ.map g) ε s).fst=
      volume.withDensity (fun y=>ENNReal.ofReal (gaussianFlightDensity μ g ε s y)) := by
  letI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  rw [(gaussianFlightLaw_conditional (μ.map g) hε s).1]
  have he:flightObservation (μ.map g) ε s=
      gaussianObservationJoint (μ.map g)
        (isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne')
        (latentCenter s) := rfl
  let e:E≃L[ℝ]E:=isotropicScale (observationNoise ε s) (observationNoise_pos hε s).ne'
  have hM:Measurable (latentCenter (E:=E) s) := by unfold latentCenter; fun_prop
  have hj:gaussianObservationJoint (μ.map g) e (latentCenter s)=
      (volume.prod (μ.map g)).withDensity (fun q:E×(E×E)=>affineGaussianDensity e (latentCenter s q.2) q.1) :=
    gaussian_observation_joint_density (μ.map g) e hM
  have hf:=fst_withDensity_prod volume (μ.map g)
    (fun q:E×(E×E)=>affineGaussianDensity e (latentCenter s q.2) q.1)
    (gaussian_likelihood_measurable e hM)
  rw [he]
  change (gaussianObservationJoint (μ.map g) e (latentCenter s)).fst=_
  rw [hj,hf]
  apply congrArg (fun r:E→ℝ≥0∞=>(volume:Measure E).withDensity r)
  funext y
  have hm:Measurable (fun z:E×E=>affineGaussianDensity e (latentCenter s z) y) := by
    unfold affineGaussianDensity
    exact (measurable_ellipticHeat e 1).comp (measurable_const.sub hM)
  rw [lintegral_map hm hg.measurable]
  change (∫⁻ z, affineGaussianDensity (isotropicScale (observationNoise ε s)
    (observationNoise_pos hε s).ne') (latentCenter s (g z)) y ∂μ)=_
  simp_rw [← singleFlightDensity_eq_gaussian hε]
  exact (ofReal_integral_eq_lintegral_ofReal
    (singleFlightDensity_latent_integrable μ g hg hε.ne' s y)
    (Filter.Eventually.of_forall (fun z=>(singleFlightDensity_pos hε s y (g z)).le))).symm

end PersistencePays
#print axioms PersistencePays.gaussianFlightLaw_fst_density
#print axioms PersistencePays.gaussianFlightDensity_contDiff
