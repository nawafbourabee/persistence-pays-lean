import PersistencePays.ComparisonMomentIteration
import PersistencePays.DensityCapPropagation

/-! Full Lemma 5.11, combining actual quantitative moments and density cap. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.lemma_5_11 {U : E → ℝ} {L LH h vstar R : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hL : h^2*L ≤ 1/64) (hh : 0 < h) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h)
    (z : E×E) (hz : phaseEnergy U z ≤ R) (n N : ℕ) (hn : n+1 ≤ N) :
    let r := Real.exp (-h)
    let σ := Real.sqrt (1-Real.exp (-2*h))
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let P := gaussianSandwichKernel e e.measurable r σ
    let μ₁ := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ z
    let μ := iterateKernel P n ∘ₘ μ₁
    let ν := phaseOUKernel r σ ∘ₘ μ
    secondMomentNorm μ (modifiedEnergy U h) ≤
      (1.008:ℝ)*Real.exp ((0.081:ℝ)*(((n:ℝ)+1)*h))*
        (R+2*((Module.finrank ℝ E : ℝ)+2)*(((n:ℝ)+1)*h)) ∧
    secondMomentNorm ν (modifiedEnergy U h) ≤
      (1.01:ℝ)*Real.exp ((0.081:ℝ)*((N:ℝ)*h))*
        (R+2*((Module.finrank ℝ E : ℝ)+2)*((N:ℝ)*h+1)) ∧
    ∃ f : E×E → ℝ≥0∞, Measurable f ∧
      ν = ((volume : Measure E).prod volume).withDensity f ∧
      ∀ w, f w ≤ ENNReal.ofReal ((((2*Real.pi*h*σ^2)^Module.finrank ℝ E)⁻¹)*
        Real.exp (2*(Module.finrank ℝ E : ℝ)*((N:ℝ)*h))) := by
  have hm := a.lemma_5_11_moments a2 hstar hzero hL hh hLH hscale z hz n N hn
  refine ⟨hm.1, hm.2, ?_⟩
  apply lemma_5_11_density _ _ h _ vstar hh _ z n N hn
  apply Real.sqrt_pos.mpr
  have he : Real.exp (-2*h)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

end PersistencePays
#print axioms PersistencePays.A1.lemma_5_11
