import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod

/-! Bayes' formula for a genuine joint law with an exponential likelihood.
The posterior is an actual Markov kernel, identified with condKernel. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {Y Z:Type*} [MeasurableSpace Y] [MeasurableSpace Z]

def latentNormalizer (μ:Measure Z) (ψ:Y×Z→ℝ) (y:Y):ℝ :=
  ∫ z,Real.exp (ψ (y,z)) ∂μ

def latentPosteriorKernel (μ:Measure Z) [IsProbabilityMeasure μ] (ψ:Y×Z→ℝ) : Kernel Y Z :=
  (Kernel.const Y μ).withDensity (fun y z =>
    ENNReal.ofReal (Real.exp (ψ (y,z))/latentNormalizer μ ψ y))

lemma latentNormalizer_measurable (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ) : Measurable (latentNormalizer μ ψ) := by
  exact hψ.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma latentPosterior_density_measurable (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ) :
    Measurable (fun q:Y×Z => ENNReal.ofReal (Real.exp (ψ q)/latentNormalizer μ ψ q.1)) :=
  (hψ.exp.div ((latentNormalizer_measurable μ hψ).comp measurable_fst)).ennreal_ofReal

lemma latentPosteriorKernel_apply (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ) (y:Y) :
    latentPosteriorKernel μ ψ y=μ.tilted (fun z => ψ (y,z)) := by
  rw [latentPosteriorKernel,Kernel.withDensity_apply _ (latentPosterior_density_measurable μ hψ)]
  rfl

lemma latentPosteriorKernel_markov (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ)
    (hi:∀ y,Integrable (fun z => Real.exp (ψ (y,z))) μ) :
    IsMarkovKernel (latentPosteriorKernel μ ψ) := by
  constructor
  intro y
  rw [latentPosteriorKernel_apply μ hψ]
  exact isProbabilityMeasure_tilted (hi y)

/-- An actual joint density factors as its marginal density times the
normalized exponential posterior. -/
theorem latent_bayes_factorization (η:Measure Y) [SFinite η]
    (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ)
    (hi:∀ y,Integrable (fun z => Real.exp (ψ (y,z))) μ)
    {c:Y→ℝ} (hc:Measurable c) (hc0:∀ y,0≤c y) :
    (η.prod μ).withDensity (fun q => ENNReal.ofReal (c q.1*Real.exp (ψ q)))=
      (η.withDensity (fun y => ENNReal.ofReal (c y*latentNormalizer μ ψ y))) ⊗ₘ
        latentPosteriorKernel μ ψ := by
  letI := latentPosteriorKernel_markov μ hψ hi
  letI : IsMarkovKernel ((Kernel.const Y μ).withDensity (fun y z =>
      ENNReal.ofReal (Real.exp (ψ (y,z))/latentNormalizer μ ψ y))) :=
    latentPosteriorKernel_markov μ hψ hi
  have hden:Measurable (fun y => ENNReal.ofReal (c y*latentNormalizer μ ψ y)) :=
    (hc.mul (latentNormalizer_measurable μ hψ)).ennreal_ofReal
  have hZ:∀ y,0<latentNormalizer μ ψ y := fun y => integral_exp_pos (hi y)
  rw [latentPosteriorKernel,Measure.compProd_withDensity
    (latentPosterior_density_measurable μ hψ),Measure.compProd_const,
    prod_withDensity_left hden,
    ← withDensity_mul]
  · congr 1
    funext q
    simp only [Pi.mul_apply,Prod.mk.eta]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hc0 q.1) (hZ q.1).le)]
    congr 1
    field_simp [(hZ q.1).ne']
  · exact hden.comp measurable_fst
  · exact latentPosterior_density_measurable μ hψ

/-- The normalized exponential likelihood is the actual conditional law. -/
theorem latent_bayes_condKernel [StandardBorelSpace Z] [Nonempty Z]
    (η:Measure Y) [SFinite η] (μ:Measure Z) [IsProbabilityMeasure μ]
    (ρ:Measure (Y×Z)) [IsFiniteMeasure ρ]
    {ψ:Y×Z→ℝ} (hψ:Measurable ψ)
    (hi:∀ y,Integrable (fun z => Real.exp (ψ (y,z))) μ)
    {c:Y→ℝ} (hc:Measurable c) (hc0:∀ y,0≤c y)
    (hρ:ρ=(η.prod μ).withDensity (fun q => ENNReal.ofReal (c q.1*Real.exp (ψ q)))) :
    ρ.fst=η.withDensity (fun y => ENNReal.ofReal (c y*latentNormalizer μ ψ y)) ∧
    ∀ᵐ y ∂ρ.fst,ρ.condKernel y=μ.tilted (fun z => ψ (y,z)) := by
  letI := latentPosteriorKernel_markov μ hψ hi
  have hf := hρ.trans (latent_bayes_factorization η μ hψ hi hc hc0)
  have hm := congrArg Measure.fst hf
  rw [Measure.fst_compProd] at hm
  refine ⟨hm,?_⟩
  have hh := eq_condKernel_of_measure_eq_compProd (latentPosteriorKernel μ ψ)
    (hm ▸ hf)
  filter_upwards [hh] with y hy
  rw [← hy,latentPosteriorKernel_apply μ hψ]

end
end PersistencePays
#print axioms PersistencePays.latent_bayes_condKernel
