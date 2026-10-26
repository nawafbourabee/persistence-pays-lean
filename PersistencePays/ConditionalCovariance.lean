import PersistencePays.ConditionalLawBounds

/-! Gaussian covariance duality for the actual velocity disintegration, with
an x-dependent measurable positive-definite self-adjoint field. The signed
covariance term and log determinant must be integrable; these are precisely
the integrability obligations supplied by Appendix A's preceding analysis. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def conditionalCovarianceContraction (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (G : E → (E →L[ℝ] E)) (x : E) : ℝ :=
  covarianceContraction (μ.condKernel x) (LinearMap.id-(G x).toLinearMap)

lemma conditionalCovarianceContraction_measurable (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (G : E → (E →L[ℝ] E)) (hG : Measurable G) :
    Measurable (conditionalCovarianceContraction μ G) := by
  have hm : Measurable (fun x => ∫ v:E,v ∂μ.condKernel x) :=
    stronglyMeasurable_id.integral_kernel.measurable
  have hh : Measurable (fun z:E×E =>
      ⟪z.2-(∫ v:E,v ∂μ.condKernel z.1),
        (z.2-(∫ v:E,v ∂μ.condKernel z.1))-
          (G z.1) (z.2-(∫ v:E,v ∂μ.condKernel z.1))⟫_ℝ) := by
    have hu : Measurable (fun z:E×E => z.2-(∫ v:E,v ∂μ.condKernel z.1)) :=
      measurable_snd.sub (hm.comp measurable_fst)
    have happ : Measurable (fun z:E×E =>
        (G z.1) (z.2-(∫ v:E,v ∂μ.condKernel z.1))) :=
      (continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hG.comp measurable_fst).prodMk hu)
    exact hu.inner (hu.sub happ)
  have hi := hh.stronglyMeasurable.integral_kernel_prod_right' (κ:=μ.condKernel)
  exact hi.measurable

/-- The matrix inequality holds for the actual conditional law at almost every
position; second moments and finite fiber entropy are conclusions of disintegration. -/
theorem conditional_covariance_entropy_ae (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞)
    (G : E → (E →L[ℝ] E))
    (hG : ∀ᵐ x ∂μ.fst,(G x).toLinearMap.IsSymmetric ∧
      ∀ v:E,v ≠ 0 → 0<⟪v,(G x) v⟫_ℝ) :
    ∀ᵐ x ∂μ.fst,conditionalCovarianceContraction μ G x ≤
      4*(klDiv (μ.condKernel x) (stdGaussian E)).toReal-
        2*‖∫ v,v ∂μ.condKernel x‖^2-Real.log (LinearMap.det (G x).toLinearMap) := by
  filter_upwards [conditional_laws_second_moments μ hm,conditional_laws_finite_entropy μ hD,hG]
    with x hx hdx hGx
  exact gaussian_covariance_entropy_logdet (μ.condKernel x) hx hdx
    (G x).toLinearMap hGx.1 hGx.2

/-- The integrated Gaussian-duality contribution to Lemma A.1.
No Brenier map or integration-by-parts inequality is assumed here. -/
theorem conditional_covariance_entropy_integral (μ : Measure (E×E)) [IsProbabilityMeasure μ]
    (hm : MemLp id 2 μ) (hD : conditionalGaussianEntropy μ (stdGaussian E) 0 ≠ ∞)
    (G : E → (E →L[ℝ] E)) (hGmeas : Measurable G)
    (hG : ∀ᵐ x ∂μ.fst,(G x).toLinearMap.IsSymmetric ∧
      ∀ v:E,v ≠ 0 → 0<⟪v,(G x) v⟫_ℝ)
    (hC : HasFiniteIntegral (conditionalCovarianceContraction μ G) μ.fst)
    (hlog : Integrable (fun x => Real.log (LinearMap.det (G x).toLinearMap)) μ.fst) :
    (∫ x,conditionalCovarianceContraction μ G x ∂μ.fst) ≤
      4*(conditionalGaussianEntropy μ (stdGaussian E) 0).toReal-
        2*(conditionalMeanSquare μ).toReal-
          ∫ x,Real.log (LinearMap.det (G x).toLinearMap) ∂μ.fst := by
  have hCi : Integrable (conditionalCovarianceContraction μ G) μ.fst :=
    ⟨(conditionalCovarianceContraction_measurable μ G hGmeas).aestronglyMeasurable,hC⟩
  have hK := conditional_kl_integral μ hD
  have hJ := conditional_mean_square_integral μ hm hD
  have hb := integral_mono_ae hCi (((hK.1.const_mul 4).sub (hJ.1.const_mul 2)).sub hlog)
    (conditional_covariance_entropy_ae μ hm hD G hG)
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (f:=fun x => 4*(klDiv (μ.condKernel x) (stdGaussian E)).toReal-
        2*‖∫ v,v ∂μ.condKernel x‖^2)
      (g:=fun x => Real.log (LinearMap.det (G x).toLinearMap))
      ((hK.1.const_mul 4).sub (hJ.1.const_mul 2)) hlog,
    integral_sub (f:=fun x => 4*(klDiv (μ.condKernel x) (stdGaussian E)).toReal)
      (g:=fun x => 2*‖∫ v,v ∂μ.condKernel x‖^2)
      (hK.1.const_mul 4) (hJ.1.const_mul 2),
    integral_const_mul,integral_const_mul,hK.2,hJ.2] at hb
  exact hb

end PersistencePays
#print axioms PersistencePays.conditional_covariance_entropy_ae
#print axioms PersistencePays.conditional_covariance_entropy_integral
