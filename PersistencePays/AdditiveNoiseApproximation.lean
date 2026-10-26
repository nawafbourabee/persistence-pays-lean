import PersistencePays.TruncationApproximation
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Actual additive-noise regularization, including joint weak continuity. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]

def additiveNoiseProbability (μ γ : ProbabilityMeasure S) (ε : ℝ) : ProbabilityMeasure S :=
  (μ.prod γ).map (show Measurable (fun z : S×S => z.1+ε•z.2) by fun_prop).aemeasurable

@[simp] theorem additiveNoiseProbability_coe (μ γ : ProbabilityMeasure S) (ε : ℝ) :
    (additiveNoiseProbability μ γ ε : Measure S) =
      ((μ : Measure S).prod (γ : Measure S)).map (fun z : S×S => z.1+ε•z.2) := rfl

theorem additiveNoiseProbability_zero (μ γ : ProbabilityMeasure S) :
    additiveNoiseProbability μ γ 0 = μ := by
  apply Subtype.ext
  change ((μ : Measure S).prod (γ : Measure S)).map (fun z : S×S => z.1+0•z.2) = _
  simp only [zero_smul,add_zero,Measure.map_fst_prod,measure_univ,one_smul]
  rfl

theorem additiveNoiseProbability_lift (μ γ : ProbabilityMeasure S) (ε : ℝ) :
    additiveNoiseProbability μ γ ε =
      ((diracProba ε).prod (μ.prod γ)).map
        (show Measurable (fun z : ℝ×(S×S) => z.2.1+z.1•z.2.2) by fun_prop).aemeasurable := by
  apply Subtype.ext
  change ((μ : Measure S).prod (γ : Measure S)).map (fun z : S×S => z.1+ε•z.2) =
    ((Measure.dirac ε).prod ((μ : Measure S).prod (γ : Measure S))).map
      (fun z : ℝ×(S×S) => z.2.1+z.1•z.2.2)
  rw [Measure.dirac_prod,Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

theorem additiveNoiseProbability_tendsto (μn : ℕ → ProbabilityMeasure S)
    (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ) {e : ℝ}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hε : Tendsto ε atTop (𝓝 e)) :
    Tendsto (fun n => additiveNoiseProbability (μn n) γ (ε n)) atTop
      (𝓝 (additiveNoiseProbability μ γ e)) := by
  simp_rw [additiveNoiseProbability_lift]
  have hprod : Tendsto (fun n => (μn n).prod γ) atTop (𝓝 (μ.prod γ)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (hμ.prodMk_nhds tendsto_const_nhds)
  have hdirac : Tendsto (fun n => diracProba (ε n)) atTop (𝓝 (diracProba e)) :=
    continuous_diracProba.continuousAt.tendsto.comp hε
  have hh : Tendsto (fun n => (diracProba (ε n)).prod ((μn n).prod γ)) atTop
      (𝓝 ((diracProba e).prod (μ.prod γ))) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (hdirac.prodMk_nhds hprod)
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hh (by fun_prop)

theorem additiveNoiseProbability_memLp (μ γ : ProbabilityMeasure S) (ε : ℝ)
    {p : ℝ≥0∞} (hμ : MemLp id p (μ : Measure S)) (hγ : MemLp id p (γ : Measure S)) :
    MemLp id p (additiveNoiseProbability μ γ ε : Measure S) := by
  rw [additiveNoiseProbability_coe]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  exact (hμ.comp_fst (γ : Measure S)).add ((hγ.comp_snd (μ : Measure S)).const_smul ε)

end PersistencePays
#print axioms PersistencePays.additiveNoiseProbability_tendsto
