import PersistencePays.ContinuousEntropyTests
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! Joint weak lower semicontinuity of actual relative entropy, proved through
the bounded-continuous variational formula, including infinite KL. -/
open MeasureTheory InformationTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace PersistencePays
noncomputable section
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

theorem klDiv_eq_iSup_continuous_dual [NormalSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [(μ+ν).WeaklyRegular] :
    klDiv μ ν = ⨆ f : S →ᵇ ℝ, ENNReal.ofReal (entropyDual μ ν f) := by
  apply le_antisymm
  · apply klDiv_le_of_bounded_duals μ ν
    intro f hf
    let C : ℝ≥0∞ := ⨆ g : S →ᵇ ℝ, ENNReal.ofReal (entropyDual μ ν g)
    change ENNReal.ofReal (entropyDual μ ν f) ≤ C
    by_cases hC : C = ∞
    · simp [hC]
    apply (ENNReal.ofReal_le_iff_le_toReal hC).mpr
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg⟩ := entropyDual_continuous_approx μ ν hf hε
    have hh : ENNReal.ofReal (entropyDual μ ν g) ≤ C := le_iSup_of_le g le_rfl
    have hr := (ENNReal.ofReal_le_iff_le_toReal hC).mp hh
    linarith
  · exact iSup_le (fun f => entropyDual_le_klDiv μ ν (boundedContinuous_isBoundedMeasurable f))

lemma continuous_entropyDual (f : S →ᵇ ℝ) :
    Continuous (fun p : ProbabilityMeasure S × ProbabilityMeasure S =>
      entropyDual (p.1 : Measure S) (p.2 : Measure S) f) := by
  have hμ : Continuous (fun p : ProbabilityMeasure S × ProbabilityMeasure S =>
      ∫ x, f x ∂(p.1 : Measure S)) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_fst
  have hν : Continuous (fun p : ProbabilityMeasure S × ProbabilityMeasure S =>
      ∫ x, expBoundedContinuous f x ∂(p.2 : Measure S)) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (expBoundedContinuous f)).comp continuous_snd
  exact (hμ.sub hν).add continuous_const

/-- KL is jointly lower semicontinuous for weak convergence of probability laws. -/
theorem klDiv_joint_lowerSemicontinuous [PolishSpace S] :
    LowerSemicontinuous (fun p : ProbabilityMeasure S × ProbabilityMeasure S =>
      klDiv (p.1 : Measure S) (p.2 : Measure S)) := by
  have heq : (fun p : ProbabilityMeasure S × ProbabilityMeasure S =>
      klDiv (p.1 : Measure S) (p.2 : Measure S)) =
      (fun p => ⨆ f : S →ᵇ ℝ, ENNReal.ofReal (entropyDual (p.1 : Measure S) (p.2 : Measure S) f)) := by
    funext p
    exact klDiv_eq_iSup_continuous_dual _ _
  rw [heq]
  exact lowerSemicontinuous_iSup (fun f =>
    (ENNReal.continuous_ofReal.comp (continuous_entropyDual f)).lowerSemicontinuous)

/-- The concrete sequential lower bound used in regularization arguments. -/
theorem klDiv_le_liminf [PolishSpace S]
    (μn νn : ℕ → ProbabilityMeasure S) (μ ν : ProbabilityMeasure S)
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) :
    klDiv (μ : Measure S) (ν : Measure S) ≤
      liminf (fun n => klDiv (μn n : Measure S) (νn n : Measure S)) atTop := by
  apply le_of_forall_lt
  intro b hb
  obtain ⟨c,hbc,hc⟩ := exists_between hb
  have he := (hμ.prodMk_nhds hν).eventually
    ((klDiv_joint_lowerSemicontinuous (S:=S) (μ,ν)) c hc)
  exact hbc.trans_le (le_liminf_of_le (by isBoundedDefault) (he.mono (fun _ h => h.le)))

section Conditional
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
  [PolishSpace E] [PolishSpace F]

/-- Conditional relative entropy with a fixed second-coordinate reference is
weakly lower semicontinuous, despite its moving first-marginal reference. -/
theorem conditionalKL_lowerSemicontinuous (γ : ProbabilityMeasure F) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure (E×F) =>
      klDiv (μ : Measure (E×F)) ((μ : Measure (E×F)).fst.prod (γ : Measure F))) := by
  have hm : Continuous (fun μ : ProbabilityMeasure (E×F) =>
      μ.map measurable_fst.aemeasurable) := ProbabilityMeasure.continuous_map continuous_fst
  have hr : Continuous (fun μ : ProbabilityMeasure (E×F) =>
      (μ.map measurable_fst.aemeasurable).prod γ) :=
    ProbabilityMeasure.continuous_prod.comp (hm.prodMk continuous_const)
  exact klDiv_joint_lowerSemicontinuous.comp (continuous_id.prodMk hr)

end Conditional

end
end PersistencePays
#print axioms PersistencePays.klDiv_joint_lowerSemicontinuous

#print axioms PersistencePays.conditionalKL_lowerSemicontinuous
