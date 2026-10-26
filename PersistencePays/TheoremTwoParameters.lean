import PersistencePays.UnadjustedEntropyIteration

/-! The exact Theorem 2 coefficients at arbitrary positive curvature m. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

def finiteMaxNonnegative (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((Finset.range n).sup (fun k => Real.toNNReal (f k)) : ℝ≥0)

theorem finiteMaxNonnegative_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ finiteMaxNonnegative f n :=
  NNReal.coe_nonneg _

theorem le_finiteMaxNonnegative (f : ℕ → ℝ) {k n : ℕ} (hk : k<n) : f k ≤ finiteMaxNonnegative f n := by
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast (Finset.le_sup (f := fun k => Real.toNNReal (f k)) (Finset.mem_range.mpr hk))

theorem theorem_two_parameters (m h : ℝ) (hm : 0 < m) (hh : 0 < h)
    (hhmax : Real.sqrt m*h ≤ 3/16) :
    let r := Real.exp (-(Real.sqrt m*h))
    let θ := r/16
    let rate := r^2*Real.sqrt m/(4*(16+r))
    0 < θ ∧ θ ≤ 1/16 ∧
      θ*(Real.sqrt m*h)*(13/2:ℝ) ≤ (1-r^2)/4 ∧
      2*θ*(1-r^2) ≤ r*(Real.sqrt m*h)*(1/2:ℝ)/2 ∧
      θ*r*(Real.sqrt m*h)*(1/2:ℝ)/2 ≤ (1-r^2)/4 ∧
      rate = θ*r*(1/2:ℝ)*Real.sqrt m/(2*(1+θ)) ∧
      0 < rate*h ∧ rate*h ≤ 1 ∧
      (1+θ)/(1-θ) ≤ 17/15 ∧ 1/(1-θ) ≤ 16/15 ∧
      (θ*Real.sqrt m/rate)*(13/4:ℝ) ≤ 221/(16*r) ∧
      Real.sqrt m*r^2/68 ≤ rate := by
  let t := Real.sqrt m*h
  have ht : 0 < t := mul_pos (Real.sqrt_pos.mpr hm) hh
  obtain ⟨hθ,hθu,hc1,hc2,hc3,he,hl,hr0,hr1,hp,hq,hb⟩ := theorem_two_normalized_parameters t ht hhmax
  let r := Real.exp (-t)
  let θ := r/16
  let rate0 := r^2/(4*(16+r))
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hr : 0 < r := Real.exp_pos _
  have hden : 4*(16+r) ≠ 0 := by positivity
  have hrate0 : rate0 ≠ 0 := by dsimp [rate0]; positivity
  have heRate : r^2*Real.sqrt m/(4*(16+r)) = rate0*Real.sqrt m := by dsimp [rate0]; ring
  have heTime : r^2*Real.sqrt m/(4*(16+r))*h = rate0*t := by rw [heRate]; dsimp [t]; ring
  change 0 < θ ∧ θ ≤ 1/16 ∧ _
  refine ⟨hθ,hθu,hc1,hc2,hc3,?_,?_,?_,hp,hq,?_,?_⟩
  · change θ*r*(1/2:ℝ)/(2*(1+θ))=rate0 at he
    rw [heRate,← he]
    ring
  · rwa [heTime]
  · rwa [heTime]
  · change (θ/rate0)*(13/4:ℝ) ≤ 221/(16*r) at hb
    rw [heRate, mul_div_mul_right θ rate0 hs.ne']
    exact hb
  · change r^2/68 ≤ rate0 at hl
    have hb := mul_le_mul_of_nonneg_right hl hs.le
    rw [heRate]
    nlinarith

end PersistencePays
#print axioms PersistencePays.theorem_two_parameters
