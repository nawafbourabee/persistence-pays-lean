import PersistencePays.GibbsCorrector
import PersistencePays.BrenierLogDet
import PersistencePays.BrenierMapPotential
import PersistencePays.SignedMatrixDefect
import PersistencePays.MatrixMomentBounds
import PersistencePays.CovarianceTrace

/-! Lemma A.1: the combined signed covariance defect for the actual conditional
law and canonical Brenier map. No differentiability of the Brenier map or
integrability of its Hessian is an assumption. -/
open Set Filter MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped Topology ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
open QuadraticTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem static_covariance_defect (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (ξ:ProbabilityMeasure E) (hm:MemLp id 2 μ)
    (hξ:MemLp id 2 (ξ:Measure E)) (hξac:(ξ:Measure E)≪volume)
    (hEv:conditionalGaussianEntropy μ (stdGaussian E) 0≠∞)
    (hμlog:Integrable (fun x => Real.log ((μ.fst.rnDeriv volume x).toReal)) μ.fst)
    (hξlog:Integrable (fun x => Real.log (((ξ:Measure E).rnDeriv volume x).toReal)) ξ)
    {n:E→ℝ} (hn:Measurable n) (hn0:∀ x,0<n x)
    (hν:μ.fst=volume.withDensity (fun x => ENNReal.ofReal (n x)))
    {S:E→E→L[ℝ]E} (hS:ContDiff ℝ 1 S) {C:ℝ}
    (hSb:∀ x,‖S x‖≤C*n x)
    (hdb:∀ x,‖matrixDivergence S x‖≤C*(1+‖x‖)*n x)
    (hScov:∀ᵐ x ∂μ.fst,∀ u v:E,⟪u,S x v⟫=
      n x*covarianceBilin (μ.condKernel x) u v) :
    -(∫ x,⟪x-positionBrenierMap μ ξ x,matrixDivergence S x⟫) ≤
      4*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
      2*(conditionalMeanSquare μ).toReal-
      (boltzmannEntropy μ.fst-boltzmannEntropy (ξ:Measure E)) := by
  let ν:ProbabilityMeasure E := ⟨μ.fst,inferInstance⟩
  have hνac : (ν:Measure E)≪volume := by
    change μ.fst≪volume
    rw [hν]
    exact withDensity_absolutelyContinuous _ _
  have hνca : volume≪(ν:Measure E) := by
    change volume≪μ.fst
    rw [hν]
    exact withDensity_absolutelyContinuous' hn.ennreal_ofReal.aemeasurable
      (.of_forall (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (hn0 x))))
  have hνm : MemLp id 2 (ν:Measure E) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hm.fst
  obtain ⟨s,G,hs,hs0,hG,hd,hlog,hent⟩ :=
    brenier_positive_logdet_entropy ν ξ hνm hξ hνac hνca hξac hμlog hξlog
  obtain ⟨φ,hφ,_,he⟩ := brenierMap_global_convex_gradient ν ξ hνm hξ hνac hνca
  have hpos : ∀ᵐ x ∂volume,(G x).toLinearMap.IsPositive := by
    filter_upwards [hνca.ae_le hd] with x hx
    refine ⟨hx.2.1,?_⟩
    intro v
    change 0≤⟪G x v,v⟫
    rw [real_inner_comm]
    by_cases hv:v=0
    · simp [hv]
    · exact (hx.2.2 v hv).le
  have hSp : ∀ x,(S x).toLinearMap.IsPositive := by
    apply continuous_positive_of_ae hS.continuous
    filter_upwards [hνca.ae_le hScov] with x hx
    exact covariance_field_positive (μ.condKernel x) (S x) (hn0 x).le hx
  have hiT := matrix_density_moment_integrability ν hn (fun x => (hn0 x).le) hν
    hνm (measurable_brenierMap ν ξ) (brenierMap_memLp ν ξ hνm hξ hνac) hS hSb hdb
  have hix := matrix_density_moment_integrability ν hn (fun x => (hn0 x).le) hν
    hνm measurable_id hνm hS hSb hdb
  have hdv : ∀ᵐ x ∂volume,HasFDerivWithinAt (brenierMap ν ξ) (G x) s x :=
    hνca.ae_le (hd.mono (fun x hx => hx.1))
  have hdef := signed_matrix_defect hφ (hνca.ae_le he) hs0 hG
    hdv hpos hS hSp
    hiT.1 hix.1 hiT.2.1 hix.2.1 hix.2.2
  have heC : (fun x => ((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E)
      =ᵐ[volume] (fun x => n x*conditionalCovarianceContraction μ G x) := by
    filter_upwards [hνca.ae_le hScov,hνca.ae_le hd,
      hνca.ae_le (conditional_laws_second_moments μ hm)] with x hxc hxG hxm
    exact covariance_field_trace (μ.condKernel x) hxm (S x)
      (ContinuousLinearMap.id ℝ E-G x) hxc (LinearMap.IsSymmetric.id.sub hxG.2.1)
  have hCi : Integrable (conditionalCovarianceContraction μ G) μ.fst := by
    apply (real_density_integrable_iff μ.fst hn (fun x => (hn0 x).le) hν _).mpr
    simpa only [smul_eq_mul] using hdef.1.congr heC
  have hCE := conditional_covariance_entropy_integral μ hm hEv G hG
    (hd.mono (fun x hx => hx.2)) hCi.hasFiniteIntegral hlog
  have hconv : (∫ x,((S x).comp (ContinuousLinearMap.id ℝ E-G x)).toLinearMap.trace ℝ E)=
      ∫ x,conditionalCovarianceContraction μ G x ∂μ.fst := by
    rw [integral_congr_ae heC,real_density_integral μ.fst hn (fun x => (hn0 x).le) hν]
    rfl
  rw [hconv] at hdef
  change -(∫ x,⟪x-brenierMap ν ξ x,matrixDivergence S x⟫)≤_
  change (∫ x,Real.log (LinearMap.det (G x).toLinearMap) ∂μ.fst)=
    boltzmannEntropy μ.fst-boltzmannEntropy (ξ:Measure E) at hent
  rw [hent] at hCE
  exact hdef.2.trans hCE


/-- Literal Gibbs-target form of Appendix A, Lemma A.1. The entropy and moment
hypotheses imply all logarithmic integrability used in the proof. -/
theorem A1.lemma_A_1 {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) (hK:InformationTheory.klDiv μ (phaseGibbs U)≠∞)
    {n:E→ℝ} (hn:Continuous n) (hn0:∀ x,0<n x)
    (hν:μ.fst=volume.withDensity (fun x => ENNReal.ofReal (n x)))
    {S:E→E→L[ℝ]E} (hS:ContDiff ℝ 1 S) {C:ℝ}
    (hSb:∀ x,‖S x‖≤C*n x)
    (hdb:∀ x,‖matrixDivergence S x‖≤C*(1+‖x‖)*n x)
    (hScov:∀ᵐ x ∂μ.fst,∀ u v:E,⟪u,S x v⟫=
      n x*covarianceBilin (μ.condKernel x) u v) :
    -(∫ x,⟪x-positionBrenierMap μ a.targetProbability x,matrixDivergence S x⟫) ≤
      4*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
      2*(conditionalMeanSquare μ).toReal-
      (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hf:MemLp id 2 μ.fst :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hm.fst
  exact static_covariance_defect μ a.targetProbability hm a.position_memLp_two
    (tilted_absolutelyContinuous volume (-U)) (a.velocity_entropy_finite μ hK)
    (gibbs_boltzmann_identity U a.gibbs_integrable μ.fst (a.potential_integrable hf)
      (a.position_entropy_finite μ hK)).1
    (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
      (a.potential_integrable a.position_memLp_two) (by simp)).1
    hn.measurable hn0 hν hS hSb hdb hScov

end
end PersistencePays
#print axioms PersistencePays.static_covariance_defect

#print axioms PersistencePays.A1.lemma_A_1
