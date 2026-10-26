import PersistencePays.GaussianWeightedPosterior

/-! The smooth regression covariance is the actual velocity conditional covariance. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

lemma tilted_map_comm {Z Y:Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (μ:Measure Z) {g:Z→Y} (hg:Measurable g) {ψ:Y→ℝ} (hψ:Measurable ψ) :
    (μ.tilted (ψ∘g)).map g=(μ.map g).tilted ψ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hg,lintegral_tilted,lintegral_tilted,
    integral_map hg.aemeasurable hψ.exp.aestronglyMeasurable]
  have hm:Measurable (fun x:Y=>ENNReal.ofReal (Real.exp (ψ x)/(∫z,Real.exp (ψ (g z)) ∂μ))*f x) :=
    ((hψ.exp.div_const _).ennreal_ofReal).mul hf
  rw [lintegral_map hm hg]
  rfl

universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

lemma regressionLatentMean_latent_continuous (g:Z→E×E) (hg:Continuous g) (s:ℝ) :
    Continuous (fun z=>regressionLatentMean s (g z)) := by
  unfold regressionLatentMean
  fun_prop
lemma regressionScore_latent_continuous (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) :
    Continuous (fun z=>regressionScore ε s (g z)) := by
  unfold regressionScore latentCenter
  fun_prop
lemma regressionLogWeight_latent_continuous (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) :
    Continuous (fun z=>regressionLogWeight ε s (g z)) := by
  unfold regressionLogWeight latentCenter
  fun_prop

lemma gaussianRegressionCovariance_posterior (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) (ε s:ℝ) (y u v:E) :
    ⟪u,gaussianRegressionCovariance μ g ε s y v⟫=
      covarianceBilin ((flightPosterior (μ.map g) ε s y).map (regressionLatentMean s)) u v+
        (ε^2/(1+s^2))*⟪u,v⟫ := by
  have ht:=tilted_map_comm μ hg.measurable
    (show Measurable (fun z:E×E=>regressionExponent ε s (y,z)) by
      unfold regressionExponent regressionScore regressionLogWeight latentCenter; fun_prop)
  have hm:((flightPosterior (μ.map g) ε s y).map (regressionLatentMean s))=
      (μ.tilted (fun z=>regressionExponent ε s (y,g z))).map (fun z=>regressionLatentMean s (g z)) := by
    unfold flightPosterior
    rw [←ht,Measure.map_map (regressionLatentMean_measurable s) hg.measurable]
    rfl
  rw [hm]
  exact affinePosteriorCovariance_bilin μ _ _ _
    (regressionLatentMean_latent_continuous g hg s)
    (regressionScore_latent_continuous g hg ε s)
    (regressionLogWeight_latent_continuous g hg ε s) _ y u v

theorem gaussianRegressionCovariance_actual (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:0<ε) (s:ℝ) :
    ∀ᵐ y ∂(gaussianFlightLaw (μ.map g) ε s).fst,∀u v:E,
      ⟪u,gaussianRegressionCovariance μ g ε s y v⟫=
        covarianceBilin ((gaussianFlightLaw (μ.map g) ε s).condKernel y) u v := by
  letI:IsProbabilityMeasure (μ.map g):=Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  filter_upwards [gaussianFlightLaw_conditional_moments (μ.map g) (compactLatent_memLp μ g hg) hε s]
    with y hy
  intro u v
  rw [gaussianRegressionCovariance_posterior μ g hg ε s y u v,hy.2]

end PersistencePays
#print axioms PersistencePays.gaussianRegressionCovariance_actual
