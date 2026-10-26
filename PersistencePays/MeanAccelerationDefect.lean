import PersistencePays.StaticCovarianceDefect
import PersistencePays.CorrectorConditional

/-! Conversion of the actual covariance divergence estimate into the mean-flow
acceleration term appearing in the genuine quadratic-cost expansion. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory QuadraticTransport
open scoped ENNReal RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.mean_velocity_corrector {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hm:MemLp id 2 μ)
    (hac:μ.fst≪volume) {v:E→E}
    (hv:∀ᵐ x ∂μ.fst,v x=conditionalMeanVelocity μ x) :
    (∫x,⟪v x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst)=a.corrector μ := by
  rw [A1.corrector,transportCorrector_conditional μ a.targetProbability hm a.position_memLp_two hac]
  exact integral_congr_ae (hv.mono (fun x hx=>
    congrArg (fun w:E=>⟪w,x-positionBrenierMap μ a.targetProbability x⟫) hx))

theorem A1.mean_acceleration_upper_rate {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    (hm:MemLp id 2 μ) (hK:klDiv μ (phaseGibbs U)≠∞)
    {n:E→ℝ} (hn:Continuous n) (hn0:∀x,0<n x)
    (hν:μ.fst=volume.withDensity (fun x=>ENNReal.ofReal (n x)))
    {S:E→E→L[ℝ]E} (hS:ContDiff ℝ 1 S) {C:ℝ}
    (hSb:∀x,‖S x‖≤C*n x)
    (hdb:∀x,‖matrixDivergence S x‖≤C*(1+‖x‖)*n x)
    (hScov:∀ᵐ x ∂μ.fst,∀u v:E,⟪u,S x v⟫=n x*covarianceBilin (μ.condKernel x) u v)
    {v acc:E→E} (hv:∀ᵐ x ∂μ.fst,v x=conditionalMeanVelocity μ x)
    (hacc:∀x,n x • acc x= -matrixDivergence S x) :
    (∫x,‖v x‖^2 ∂μ.fst)+
      (∫x,⟪acc x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst)≤
      6*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
      (boltzmannEntropy μ.fst-boltzmannEntropy (positionGibbs U)) := by
  have hA := a.lemma_A_1 μ hm hK hn hn0 hν hS hSb hdb hScov
  have he : (∫x,⟪acc x,x-positionBrenierMap μ a.targetProbability x⟫ ∂μ.fst)=
      -(∫x,⟪x-positionBrenierMap μ a.targetProbability x,matrixDivergence S x⟫) := by
    rw [real_density_integral μ.fst hn.measurable (fun x=>(hn0 x).le) hν]
    rw [←integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    rw [←real_inner_smul_left,hacc,inner_neg_left,real_inner_comm]
  have hJ : (∫x,‖v x‖^2 ∂μ.fst)=(conditionalMeanSquare μ).toReal := by
    rw [integral_congr_ae (hv.mono (fun x hx=>by rw [hx]))]
    exact (conditional_mean_square_integral μ hm (a.velocity_entropy_finite μ hK)).2
  rw [he,hJ]
  linarith [ENNReal.toReal_nonneg (a:=conditionalMeanSquare μ),
    ENNReal.toReal_nonneg (a:=conditionalGaussianEntropy μ (stdGaussian E) 0)]

end PersistencePays
#print axioms PersistencePays.A1.mean_velocity_corrector
#print axioms PersistencePays.A1.mean_acceleration_upper_rate
