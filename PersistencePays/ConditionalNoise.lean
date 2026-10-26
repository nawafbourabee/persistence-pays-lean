import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! Adding independent noise after a latent conditional law. All statements
identify actual joint measures and their disintegration kernels. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {Y Z R W:Type*} [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace W]

def conditionalNoiseKernel (κ:Kernel Y Z) (γ:Measure R) (f:(Y×Z)×R→W):Kernel Y W :=
  (((Kernel.id ×ₖ κ) ×ₖ Kernel.const Y γ).map f)

lemma conditionalNoiseKernel_markov (κ:Kernel Y Z) [IsMarkovKernel κ]
    (γ:Measure R) [IsProbabilityMeasure γ] {f:(Y×Z)×R→W} (hf:Measurable f) :
    IsMarkovKernel (conditionalNoiseKernel κ γ f) := by
  unfold conditionalNoiseKernel
  exact Kernel.IsMarkovKernel.map _ hf

lemma lintegral_conditionalNoiseKernel (κ:Kernel Y Z) [IsMarkovKernel κ]
    (γ:Measure R) [IsProbabilityMeasure γ] {f:(Y×Z)×R→W} (hf:Measurable f)
    {g:W→ℝ≥0∞} (hg:Measurable g) (y:Y) :
    (∫⁻ w,g w ∂conditionalNoiseKernel κ γ f y)=
      ∫⁻ z,∫⁻ r,g (f ((y,z),r)) ∂γ ∂κ y := by
  rw [conditionalNoiseKernel,Kernel.map_apply _ hf,lintegral_map hg hf,
    Kernel.prod_apply]
  rw [lintegral_prod _ (show AEMeasurable (fun q:(Y×Z)×R => g (f q)) _ from
    (hg.comp hf).aemeasurable)]
  exact Kernel.lintegral_id_prod (hg.comp hf).lintegral_prod_right' κ y

lemma conditionalNoiseKernel_apply (κ:Kernel Y Z) [IsMarkovKernel κ]
    (γ:Measure R) [IsProbabilityMeasure γ] {f:(Y×Z)×R→W} (hf:Measurable f) (y:Y) :
    conditionalNoiseKernel κ γ f y =
      ((κ y).prod γ).map (fun q:Z×R => f ((y,q.1),q.2)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_conditionalNoiseKernel κ γ hf hg y,
    lintegral_map hg (by fun_prop),lintegral_prod _ (by fun_prop)]

lemma conditionalNoise_compProd (ν:Measure Y) [SFinite ν]
    (κ:Kernel Y Z) [IsMarkovKernel κ]
    (γ:Measure R) [IsProbabilityMeasure γ] {f:(Y×Z)×R→W} (hf:Measurable f) :
    ((ν ⊗ₘ κ).prod γ).map (fun q:(Y×Z)×R => (q.1.1,f q))=
      ν ⊗ₘ conditionalNoiseKernel κ γ f := by
  letI := conditionalNoiseKernel_markov κ γ hf
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop),lintegral_prod _ (by fun_prop),
    Measure.lintegral_compProd (by fun_prop),Measure.lintegral_compProd hg]
  apply lintegral_congr
  intro y
  exact (lintegral_conditionalNoiseKernel κ γ hf
    (hg.comp (measurable_const.prodMk measurable_id)) y).symm

lemma conditionalNoise_condKernel [StandardBorelSpace Z] [Nonempty Z]
    [StandardBorelSpace W] [Nonempty W]
    (ρ:Measure (Y×Z)) [IsProbabilityMeasure ρ]
    (γ:Measure R) [IsProbabilityMeasure γ] {f:(Y×Z)×R→W} (hf:Measurable f) :
    let δ:Measure (Y×W):=(ρ.prod γ).map (fun q:(Y×Z)×R => (q.1.1,f q))
    δ.fst=ρ.fst ∧ ∀ᵐ y ∂ρ.fst,
      δ.condKernel y=((ρ.condKernel y).prod γ).map (fun q:Z×R => f ((y,q.1),q.2)) := by
  dsimp only
  let δ:Measure (Y×W):=(ρ.prod γ).map (fun q:(Y×Z)×R => (q.1.1,f q))
  letI : IsProbabilityMeasure δ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI := conditionalNoiseKernel_markov ρ.condKernel γ hf
  have he:δ=ρ.fst ⊗ₘ conditionalNoiseKernel ρ.condKernel γ f := by
    dsimp [δ]
    conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
    exact conditionalNoise_compProd ρ.fst ρ.condKernel γ hf
  have hm:δ.fst=ρ.fst := by rw [he,Measure.fst_compProd]
  refine ⟨hm,?_⟩
  have hcond := eq_condKernel_of_measure_eq_compProd (conditionalNoiseKernel ρ.condKernel γ f)
    (hm ▸ he)
  rw [hm] at hcond
  filter_upwards [hcond] with y hy
  rw [← hy,conditionalNoiseKernel_apply ρ.condKernel γ hf]

end
end PersistencePays
#print axioms PersistencePays.conditionalNoise_condKernel
