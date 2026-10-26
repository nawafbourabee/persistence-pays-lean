import PersistencePays.GaussianBridgeLaw
import PersistencePays.LatentBayes

/-! The likelihood and posterior of an actual additive Gaussian observation. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {Z:Type*} [MeasurableSpace Z]

lemma gaussian_likelihood_measurable (e:E≃L[ℝ]E) {M:Z→E} (hM:Measurable M) :
    Measurable (fun q:E×Z => affineGaussianDensity e (M q.2) q.1) := by
  exact (measurable_ellipticHeat e 1).comp (measurable_fst.sub (hM.comp measurable_snd))

lemma gaussian_observation_joint_density (μ:Measure Z) [SFinite μ]
    (e:E≃L[ℝ]E) {M:Z→E} (hM:Measurable M) :
    (μ.prod (stdGaussian E)).map (fun q:Z×E => (e q.2+M q.1,q.1))=
      (volume.prod μ).withDensity (fun q:E×Z => affineGaussianDensity e (M q.2) q.1) := by
  have hmap:Measurable (fun q:Z×E => (e q.2+M q.1,q.1)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hmap,lintegral_withDensity_eq_lintegral_mul _
    (gaussian_likelihood_measurable e hM) hf]
  change (∫⁻ q:Z×E,f (e q.2+M q.1,q.1) ∂μ.prod (stdGaussian E))=
    ∫⁻ q:E×Z,affineGaussianDensity e (M q.2) q.1*f q ∂volume.prod μ
  rw [lintegral_prod _ (show AEMeasurable (fun q:Z×E => f (e q.2+M q.1,q.1)) _ from
    (hf.comp hmap).aemeasurable),lintegral_prod_symm _
      (show AEMeasurable (fun q:E×Z => affineGaussianDensity e (M q.2) q.1*f q) _ from
        ((gaussian_likelihood_measurable e hM).mul hf).aemeasurable)]
  apply lintegral_congr
  intro z
  have hh:Measurable (fun y:E => f (y,z)) := hf.comp (measurable_id.prodMk measurable_const)
  change (∫⁻ y,f (e y+M z,z) ∂stdGaussian E)=
    ∫⁻ y,(affineGaussianDensity e (M z)*(fun y => f (y,z))) y
  rw [← lintegral_withDensity_eq_lintegral_mul _ (measurable_affineGaussianDensity e (M z)) hh,
    affineGaussianDensity_eq_map_stdGaussian,lintegral_map hh (by fun_prop)]

/-- Gaussian likelihood exponent after applying the inverse covariance square root. -/
def gaussianLikelihoodExponent (e:E≃L[ℝ]E) (M:Z→E) (q:E×Z):ℝ :=
  ⟪e.symm (M q.2),e.symm q.1⟫-‖e.symm (M q.2)‖^2/2

def gaussianLikelihoodBase (e:E≃L[ℝ]E) (y:E):ℝ :=
  (inverseJacobian e).toReal * heatReal 1 (e.symm y)

lemma inverseJacobian_pos (e:E≃L[ℝ]E) : 0<(inverseJacobian e).toReal := by
  dsimp [inverseJacobian]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  exact abs_pos.mpr (inv_ne_zero e.toLinearEquiv.isUnit_det'.ne_zero)

lemma gaussianLikelihoodBase_pos (e:E≃L[ℝ]E) (y:E) : 0<gaussianLikelihoodBase e y :=
  mul_pos (inverseJacobian_pos e) (heatReal_pos (by norm_num) _)

lemma gaussian_likelihood_factorization (e:E≃L[ℝ]E) (M:Z→E) (q:E×Z) :
    affineGaussianDensity e (M q.2) q.1 =
      ENNReal.ofReal (gaussianLikelihoodBase e q.1*Real.exp (gaussianLikelihoodExponent e M q)) := by
  have hj : inverseJacobian e = ENNReal.ofReal (inverseJacobian e).toReal := by
    dsimp [inverseJacobian]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [affineGaussianDensity,ellipticHeat,hj,heatDensity,← ENNReal.ofReal_mul (inverseJacobian_pos e).le]
  congr 1
  dsimp [gaussianLikelihoodBase,heatReal,gaussianLikelihoodExponent]
  rw [map_sub,norm_sub_sq_real,show (2:ℝ)*1=2 by norm_num]
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  rw [real_inner_comm]
  ring

lemma gaussianLikelihoodExponent_bound (e:E≃L[ℝ]E) (M:Z→E) (y:E) (z:Z) :
    gaussianLikelihoodExponent e M (y,z) ≤ ‖e.symm y‖^2/2 := by
  have hn:=sq_nonneg ‖e.symm y-e.symm (M z)‖
  rw [norm_sub_sq_real,real_inner_comm] at hn
  dsimp [gaussianLikelihoodExponent]
  linarith

lemma gaussianLikelihoodExponent_integrable (μ:Measure Z) [IsProbabilityMeasure μ]
    (e:E≃L[ℝ]E) {M:Z→E} (hM:Measurable M) (y:E) :
    Integrable (fun z => Real.exp (gaussianLikelihoodExponent e M (y,z))) μ := by
  apply (integrable_const (Real.exp (‖e.symm y‖^2/2))).mono'
    (show Measurable (fun z => Real.exp (gaussianLikelihoodExponent e M (y,z))) by
      unfold gaussianLikelihoodExponent; fun_prop).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (gaussianLikelihoodExponent_bound e M y z)


def gaussianObservationJoint (μ:Measure Z) (e:E≃L[ℝ]E) (M:Z→E):Measure (E×Z) :=
  (μ.prod (stdGaussian E)).map (fun q:Z×E => (e q.2+M q.1,q.1))

instance gaussianObservationJoint_finite (μ:Measure Z) [IsFiniteMeasure μ]
    (e:E≃L[ℝ]E) (M:Z→E) : IsFiniteMeasure (gaussianObservationJoint μ e M) := by
  unfold gaussianObservationJoint
  infer_instance

theorem gaussian_observation_posterior [StandardBorelSpace Z] [Nonempty Z]
    (μ:Measure Z) [IsProbabilityMeasure μ] (e:E≃L[ℝ]E) {M:Z→E} (hM:Measurable M) :
    (gaussianObservationJoint μ e M).fst =
      volume.withDensity (fun y => ENNReal.ofReal
        (gaussianLikelihoodBase e y*latentNormalizer μ (gaussianLikelihoodExponent e M) y)) ∧
    ∀ᵐ y ∂(gaussianObservationJoint μ e M).fst,
      (gaussianObservationJoint μ e M).condKernel y =
        μ.tilted (fun z => gaussianLikelihoodExponent e M (y,z)) := by
  letI : IsProbabilityMeasure (gaussianObservationJoint μ e M) :=
    Measure.isProbabilityMeasure_map (show Measurable (fun q:Z×E => (e q.2+M q.1,q.1)) by
      fun_prop).aemeasurable
  apply latent_bayes_condKernel volume μ (gaussianObservationJoint μ e M)
    (show Measurable (gaussianLikelihoodExponent e M) by
      unfold gaussianLikelihoodExponent; fun_prop)
    (gaussianLikelihoodExponent_integrable μ e hM)
    (show Measurable (gaussianLikelihoodBase e) by
      unfold gaussianLikelihoodBase heatReal; fun_prop)
    (fun y => (gaussianLikelihoodBase_pos e y).le)
  rw [gaussianObservationJoint,gaussian_observation_joint_density μ e hM]
  congr 1
  funext q
  exact gaussian_likelihood_factorization e M q

end
end PersistencePays
#print axioms PersistencePays.gaussian_observation_joint_density
#print axioms PersistencePays.gaussian_likelihood_factorization

#print axioms PersistencePays.gaussian_observation_posterior
