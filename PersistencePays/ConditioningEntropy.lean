import PersistencePays.ConditionalLawEntropy

/-! Lemma 5.8, with actual normalized restrictions. In fact the partition may
be any measurable event, so conditioning on speed is a special case. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def binaryEntropy (α : ℝ) : ℝ := -α*Real.log α-(1-α)*Real.log (1-α)

/-- Finite entropy relative to any product reference implies finite conditional
velocity entropy. This applies directly to the Gibbs entropy propagated by the chain. -/
theorem conditional_entropy_finite_of_full (p : Measure (E×E)) [IsProbabilityMeasure p]
    (π γ : Measure E) [IsProbabilityMeasure π] [IsProbabilityMeasure γ]
    (hD : klDiv p (π.prod γ) ≠ ∞) : klDiv p (p.fst.prod γ) ≠ ∞ := by
  rw [klDiv_product_reference_decomposition p π γ] at hD
  exact (ENNReal.add_ne_top.mp hD).2

theorem binaryEntropy_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    binaryEntropy α ≤ α*Real.log (1/α)+α := by
  by_cases h0 : α = 0
  · simp [h0, binaryEntropy]
  by_cases h1 : α = 1
  · simp [h1, binaryEntropy]
  have hp : 0 < 1-α := sub_pos.mpr (lt_of_le_of_ne hα1 h1)
  have hx := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  have hi : (1-α)*(1-α)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  rw [Real.log_div (by norm_num) h0, Real.log_one]
  unfold binaryEntropy
  nlinarith

theorem conditioning_entropy_finite (p : Measure (E×E)) [IsProbabilityMeasure p]
    (γ : Measure E) [IsProbabilityMeasure γ]
    (hD : klDiv p (p.fst.prod γ) ≠ ∞)
    (A : Set (E×E)) (hA : MeasurableSet A) (hpos : p A ≠ 0) :
    klDiv (ProbabilityTheory.cond p A) ((ProbabilityTheory.cond p A).fst.prod γ) ≠ ∞ := by
  letI : IsProbabilityMeasure (ProbabilityTheory.cond p A) := cond_isProbabilityMeasure hpos
  have hh := (conditional_klDiv p (p.fst.prod γ) hD A hA hpos).1
  rw [klDiv_product_reference_decomposition (ProbabilityTheory.cond p A) p.fst γ] at hh
  exact (ENNReal.add_ne_top.mp hh).2

theorem conditioning_entropy_bounds (p : Measure (E×E)) [IsProbabilityMeasure p]
    (γ : Measure E) [IsProbabilityMeasure γ]
    (hD : klDiv p (p.fst.prod γ) ≠ ∞)
    (A : Set (E×E)) (hA : MeasurableSet A) (hpos : p A ≠ 0) (hcomp : p Aᶜ ≠ 0) :
    let a := ProbabilityTheory.cond p Aᶜ
    let b := ProbabilityTheory.cond p A
    let α := (p A).toReal
    let E0 := (klDiv p (p.fst.prod γ)).toReal
    let Ea := (klDiv a (a.fst.prod γ)).toReal
    let Eb := (klDiv b (b.fst.prod γ)).toReal
    (1-α)*Ea+α*Eb-binaryEntropy α ≤ E0 ∧ E0 ≤ (1-α)*Ea+α*Eb := by
  dsimp only
  let a := ProbabilityTheory.cond p Aᶜ
  let b := ProbabilityTheory.cond p A
  letI : IsProbabilityMeasure a := cond_isProbabilityMeasure hcomp
  letI : IsProbabilityMeasure b := cond_isProbabilityMeasure hpos
  have hba := conditional_klDiv p (p.fst.prod γ) hD A hA hpos
  have haa := conditional_klDiv p (p.fst.prod γ) hD Aᶜ hA.compl hcomp
  have hdb := klDiv_product_reference_decomposition b p.fst γ
  have hda := klDiv_product_reference_decomposition a p.fst γ
  have hbfin : klDiv b.fst p.fst ≠ ∞ ∧ klDiv b (b.fst.prod γ) ≠ ∞ := by
    apply ENNReal.add_ne_top.mp
    rw [← hdb]
    exact hba.1
  have hafin : klDiv a.fst p.fst ≠ ∞ ∧ klDiv a (a.fst.prod γ) ≠ ∞ := by
    apply ENNReal.add_ne_top.mp
    rw [← hda]
    exact haa.1
  have hbReal : (klDiv b (p.fst.prod γ)).toReal =
      (klDiv b.fst p.fst).toReal+(klDiv b (b.fst.prod γ)).toReal := by
    rw [hdb, ENNReal.toReal_add hbfin.1 hbfin.2]
  have haReal : (klDiv a (p.fst.prod γ)).toReal =
      (klDiv a.fst p.fst).toReal+(klDiv a (a.fst.prod γ)).toReal := by
    rw [hda, ENNReal.toReal_add hafin.1 hafin.2]
  have hsb := conditional_klDiv_self p A hA hpos
  have hsa := conditional_klDiv_self p Aᶜ hA.compl hcomp
  have hmb : (klDiv b.fst p.fst).toReal ≤ -Real.log ((p A).toReal) := by
    have hh := ENNReal.toReal_mono hsb.1 (klDiv_map_le b p measurable_fst)
    simpa only [hsb.2, Measure.fst] using hh
  have hma : (klDiv a.fst p.fst).toReal ≤ -Real.log ((p Aᶜ).toReal) := by
    have hh := ENNReal.toReal_mono hsa.1 (klDiv_map_le a p measurable_fst)
    simpa only [hsa.2, Measure.fst] using hh
  have hpart := conditional_klDiv_partition p (p.fst.prod γ) hD A hA hpos hcomp
  change (p A).toReal*(klDiv b (p.fst.prod γ)).toReal+
    (p Aᶜ).toReal*(klDiv a (p.fst.prod γ)).toReal = _ at hpart
  rw [hbReal,haReal] at hpart
  have hc := probability_complement_toReal p A hA
  have ha0 : 0 ≤ (p Aᶜ).toReal := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ (p A).toReal := ENNReal.toReal_nonneg
  have hmalo := mul_nonneg ha0 (ENNReal.toReal_nonneg (a:=klDiv a.fst p.fst))
  have hmblo := mul_nonneg hb0 (ENNReal.toReal_nonneg (a:=klDiv b.fst p.fst))
  have hmaup := mul_le_mul_of_nonneg_left hma ha0
  have hmbup := mul_le_mul_of_nonneg_left hmb hb0
  change (1-(p A).toReal)*(klDiv a (a.fst.prod γ)).toReal+
      (p A).toReal*(klDiv b (b.fst.prod γ)).toReal-binaryEntropy (p A).toReal ≤ _ ∧ _
  rw [← hc]
  unfold binaryEntropy
  rw [← hc]
  constructor <;> nlinarith

/-- The exact notation of Lemma 5.8 for a standard Gaussian velocity reference. -/
theorem lemma_5_8 (p : Measure (E×E)) [IsProbabilityMeasure p]
    (hD : conditionalGaussianEntropy p (stdGaussian E) 0 ≠ ∞)
    (A : Set (E×E)) (hA : MeasurableSet A) (hpos : p A ≠ 0) (hcomp : p Aᶜ ≠ 0) :
    let a := ProbabilityTheory.cond p Aᶜ
    let b := ProbabilityTheory.cond p A
    let α := (p A).toReal
    (1-α)*(conditionalGaussianEntropy a (stdGaussian E) 0).toReal+
      α*(conditionalGaussianEntropy b (stdGaussian E) 0).toReal-binaryEntropy α ≤
        (conditionalGaussianEntropy p (stdGaussian E) 0).toReal ∧
    (conditionalGaussianEntropy p (stdGaussian E) 0).toReal ≤
      (1-α)*(conditionalGaussianEntropy a (stdGaussian E) 0).toReal+
        α*(conditionalGaussianEntropy b (stdGaussian E) 0).toReal := by
  have hd : klDiv p (p.fst.prod (stdGaussian E)) ≠ ∞ := by
    simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] using hD
  simpa only [conditionalGaussianEntropy, transportJoint_zero, transportPosition_zero] using
    conditioning_entropy_bounds p (stdGaussian E) hd A hA hpos hcomp

/-- The same actual conditional-law bounds, with a full product-reference entropy
hypothesis; no finiteness of the conditional laws is assumed. -/
theorem conditioning_entropy_bounds_of_full (p : Measure (E×E)) [IsProbabilityMeasure p]
    (π γ : Measure E) [IsProbabilityMeasure π] [IsProbabilityMeasure γ]
    (hD : klDiv p (π.prod γ) ≠ ∞)
    (A : Set (E×E)) (hA : MeasurableSet A) (hpos : p A ≠ 0) (hcomp : p Aᶜ ≠ 0) :
    let a := ProbabilityTheory.cond p Aᶜ
    let b := ProbabilityTheory.cond p A
    let α := (p A).toReal
    let E0 := (klDiv p (p.fst.prod γ)).toReal
    let Ea := (klDiv a (a.fst.prod γ)).toReal
    let Eb := (klDiv b (b.fst.prod γ)).toReal
    (1-α)*Ea+α*Eb-binaryEntropy α ≤ E0 ∧ E0 ≤ (1-α)*Ea+α*Eb :=
  conditioning_entropy_bounds p γ (conditional_entropy_finite_of_full p π γ hD)
    A hA hpos hcomp

end PersistencePays
#print axioms PersistencePays.lemma_5_8
