import PersistencePays.GaussianUpdateSemigroup
import PersistencePays.FunctionalEntropyKL

/-! Functional and probability-law versions of the Mehler average. -/
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section

theorem entropy_comp_measurePreserving {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {μ : Measure S} {ν : Measure T} {F : S → T} (hF : MeasurePreserving F μ ν)
    (f : T → ℝ) (hf : Measurable f) :
    LogSobolev.entropy μ (f ∘ F) = LogSobolev.entropy ν f := by
  have hh (g : T → ℝ) (hg : Measurable g) : (∫ x, g (F x) ∂μ) = ∫ x, g x ∂ν := by
    rw [← hF.map_eq]
    exact (integral_map hF.measurable.aemeasurable hg.aestronglyMeasurable).symm
  unfold LogSobolev.entropy
  simp only [Function.comp_apply]
  rw [hh f hf, hh (fun x => f x * log (f x)) (by fun_prop)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianAverage (r σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ y, f (r • x + σ • y) ∂stdGaussian E

lemma measurable_gaussianAverage (r σ : ℝ) (f : E → ℝ) (hf : Measurable f) :
    Measurable (gaussianAverage r σ f) := by
  have hh : StronglyMeasurable (fun z : E × E => f (r • z.1 + σ • z.2)) :=
    (hf.comp (by fun_prop)).stronglyMeasurable
  exact hh.integral_prod_right'.measurable

lemma integrable_gaussianAverage (r σ : ℝ) (hn : r^2+σ^2=1)
    (f : E → ℝ) (hi : Integrable f (stdGaussian E)) :
    Integrable (gaussianAverage r σ f) (stdGaussian E) :=
  ((gaussianOU_preserving r σ hn).integrable_comp_of_integrable hi).integral_prod_left

theorem gaussianUpdate_real_density (r σ : ℝ) (hn : r^2+σ^2=1) (hσ : 0 ≤ σ)
    (f : E → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (hi : Integrable f (stdGaussian E)) :
    gaussianUpdate r σ ((stdGaussian E).withDensity (fun x => ENNReal.ofReal (f x))) =
      (stdGaussian E).withDensity (fun x => ENNReal.ofReal (gaussianAverage r σ f x)) := by
  rw [gaussianUpdate_density r σ hn hσ _ hf.ennreal_ofReal]
  apply withDensity_congr_ae
  have hprod := (gaussianOU_preserving r σ hn).integrable_comp_of_integrable hi
  filter_upwards [hprod.prod_right_ae] with x hx
  exact (ofReal_integral_eq_lintegral_ofReal hx (Filter.Eventually.of_forall (fun y => hfn _))).symm

end
end PersistencePays
#print axioms PersistencePays.gaussianUpdate_real_density
