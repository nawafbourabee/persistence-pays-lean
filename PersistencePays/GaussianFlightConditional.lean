import PersistencePays.GaussianRegressionLaw
import PersistencePays.IsotropicObservation
import PersistencePays.ConditionalNoise

/-! The actual free-flight law after Gaussian smoothing has the Gaussian-mixture
conditional velocity distribution asserted in Appendix A.2. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianFlightLaw (μ:Measure (E×E)) (ε s:ℝ):Measure (E×E) :=
  (μ.prod ((stdGaussian E).prod (stdGaussian E))).map
    (fun q:(E×E)×(E×E) => latentFlight ε s q.1 q.2)

instance gaussianFlightLaw_finite (μ:Measure (E×E)) [IsFiniteMeasure μ] (ε s:ℝ) :
    IsFiniteMeasure (gaussianFlightLaw μ ε s) := by unfold gaussianFlightLaw; infer_instance
instance gaussianFlightLaw_probability (μ:Measure (E×E)) [IsProbabilityMeasure μ] (ε s:ℝ) :
    IsProbabilityMeasure (gaussianFlightLaw μ ε s) := by
  unfold gaussianFlightLaw
  exact Measure.isProbabilityMeasure_map (by unfold latentFlight; fun_prop)

def regressionVelocity (ε s:ℝ) (q:(E×(E×E))×E):E :=
  regressionBeta s•q.1.1+regressionLatentMean s q.1.2+regressionNoise ε s•q.2

lemma regressionVelocity_measurable (ε s:ℝ) : Measurable (regressionVelocity (E:=E) ε s) := by
  unfold regressionVelocity regressionLatentMean
  fun_prop

lemma gaussianFlightLaw_as_regression (μ:Measure (E×E)) [IsProbabilityMeasure μ] (ε s:ℝ) :
    gaussianFlightLaw μ ε s=(μ.prod ((stdGaussian E).prod (stdGaussian E))).map
      (fun q:(E×E)×(E×E) => latentRegression ε s q.1 q.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [gaussianFlightLaw,lintegral_map hf (by unfold latentFlight; fun_prop),
    lintegral_map hf (by unfold latentRegression latentCenter regressionLatentMean; fun_prop)]
  rw [lintegral_prod _ (by unfold latentFlight; fun_prop),
    lintegral_prod _ (by unfold latentRegression latentCenter regressionLatentMean; fun_prop)]
  apply lintegral_congr
  intro z
  rw [← lintegral_map hf (by unfold latentFlight; fun_prop),latentFlight_law,
    lintegral_map hf (by unfold latentRegression; fun_prop)]

lemma gaussianFlightLaw_observation (μ:Measure (E×E)) [IsProbabilityMeasure μ] (ε s:ℝ) :
    gaussianFlightLaw μ ε s=
      ((flightObservation μ ε s).prod (stdGaussian E)).map
        (fun q:(E×(E×E))×E => (q.1.1,regressionVelocity ε s q)) := by
  rw [gaussianFlightLaw_as_regression]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by unfold latentRegression latentCenter regressionLatentMean; fun_prop),
    lintegral_map hf (by exact measurable_fst.fst.prodMk (regressionVelocity_measurable ε s))]
  rw [lintegral_prod _ (by unfold latentRegression latentCenter regressionLatentMean; fun_prop),
    lintegral_prod _ (by exact (hf.comp (measurable_fst.fst.prodMk
      (regressionVelocity_measurable ε s))).aemeasurable)]
  have hfi:Measurable (fun x:E×(E×E) => ∫⁻ y:E,f (x.1,regressionVelocity ε s (x,y)) ∂stdGaussian E) :=
    (hf.comp (measurable_fst.fst.prodMk (regressionVelocity_measurable ε s))).lintegral_prod_right'
  rw [flightObservation,lintegral_map hfi (by unfold latentCenter; fun_prop),
    lintegral_prod _ (by unfold latentCenter regressionVelocity regressionLatentMean; fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_prod _ (by unfold latentRegression latentCenter regressionLatentMean; fun_prop)]
  apply lintegral_congr
  intro η
  apply lintegral_congr
  intro ζ
  congr 1
  dsimp [latentRegression,regressionVelocity]
  rw [add_comm (observationNoise ε s•η)]

/-- Exact free-transport interpretation of the law used here. -/
lemma gaussianFlightLaw_transport (μ:Measure (E×E)) [IsProbabilityMeasure μ] (ε s:ℝ) :
    gaussianFlightLaw μ ε s=transportJoint (fullGaussianOUKernel 1 ε ∘ₘ μ) s := by
  rw [fullGaussianOUKernel_comp_map,transportJoint,
    Measure.map_map (measurable_freeTransport s) (by fun_prop)]
  unfold gaussianFlightLaw
  congr 1
  funext q
  simp only [Function.comp_apply,one_smul]
  rfl

/-- Actual conditional velocity law: posterior over the latent point, followed
by an independent isotropic Gaussian regression residual. -/
theorem gaussianFlightLaw_conditional (μ:Measure (E×E)) [IsProbabilityMeasure μ]
    {ε:ℝ} (hε:0<ε) (s:ℝ) :
    (gaussianFlightLaw μ ε s).fst=(flightObservation μ ε s).fst ∧
    ∀ᵐ y ∂(gaussianFlightLaw μ ε s).fst,
      (gaussianFlightLaw μ ε s).condKernel y=
        ((μ.tilted (fun z => regressionExponent ε s (y,z))).prod (stdGaussian E)).map
          (fun q:(E×E)×E => regressionBeta s•y+regressionLatentMean s q.1+
            regressionNoise ε s•q.2) := by
  have hh:=conditionalNoise_condKernel (flightObservation μ ε s) (stdGaussian E)
    (regressionVelocity_measurable ε s)
  dsimp only at hh
  have hh' : (gaussianFlightLaw μ ε s).fst=(flightObservation μ ε s).fst ∧
      ∀ᵐ y ∂(flightObservation μ ε s).fst,
      (gaussianFlightLaw μ ε s).condKernel y=(((flightObservation μ ε s).condKernel y).prod (stdGaussian E)).map
        (fun q:(E×E)×E => regressionVelocity ε s ((y,q.1),q.2)) := by
    simpa only [← gaussianFlightLaw_observation μ ε s] using hh
  refine ⟨hh'.1,?_⟩
  rw [hh'.1]
  filter_upwards [hh'.2,flightObservation_posterior μ hε s] with y hy hp
  rw [hy,hp]
  rfl

end
end PersistencePays
#print axioms PersistencePays.gaussianFlightLaw_conditional
#print axioms PersistencePays.gaussianFlightLaw_transport
