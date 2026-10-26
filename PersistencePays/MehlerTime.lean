import PersistencePays.MehlerDifferentiation
import PersistencePays.GaussianOU
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual Ornstein--Uhlenbeck Mehler average and its time derivative. -/
open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def mehler (t : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ y, f (exp (-t) • x + sqrt (1-exp (-2*t)) • y) ∂stdGaussian E

lemma hasDerivAt_ou_noise {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => sqrt (1-exp (-2*s)))
      (exp (-2*t) / sqrt (1-exp (-2*t))) t := by
  have hp : 0 < 1-exp (-2*t) := by
    have := exp_lt_one_iff.mpr (show -2*t < 0 by linarith)
    linarith
  convert! (((hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_id t).const_mul (-2)).exp)).sqrt hp.ne') using 1 <;>
    simp only [Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

/-- Time differentiation is justified by a Gaussian-integrable bound on an
explicit neighborhood separated from zero. -/
theorem hasDerivAt_mehler (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    {A B : ℝ} (hA : 0 ≤ A) (hfB : ∀ z, ‖f z‖ ≤ B)
    (hfA : ∀ z, ‖fderiv ℝ f z‖ ≤ A) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => mehler s f x)
      (∫ y, fderiv ℝ f (exp (-t) • x + sqrt (1-exp (-2*t)) • y)
        ((-exp (-t)) • x + (exp (-2*t)/sqrt (1-exp (-2*t))) • y)
        ∂stdGaussian E) t := by
  let l := sqrt (1-exp (-t))
  have hl : 0 < l := by
    apply sqrt_pos.2
    have := exp_lt_one_iff.mpr (neg_neg_of_pos ht)
    linarith
  let C := 1 + 1/l
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply hasDerivAt_gaussian_affine_average f hf hA hC hfB hfA
    (fun s => exp (-s)) (fun s => sqrt (1-exp (-2*s)))
    (fun s => -exp (-s)) (fun s => exp (-2*s)/sqrt (1-exp (-2*s)))
    (I := Set.Ioo (t/2) (t+1)) (Ioo_mem_nhds (by linarith) (by linarith))
  · intro s _
    convert! ((hasDerivAt_id s).neg.exp) using 1 <;>
      simp only [Pi.neg_apply, id_eq] <;> ring
  · intro s hs
    exact hasDerivAt_ou_noise (by linarith [hs.1])
  · intro s hs
    have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    calc
      exp (-s) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hs0)
      _ ≤ C := by
        dsimp [C]
        have hh : 0 ≤ 1/l := by positivity
        linarith
  · intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hden : l ≤ sqrt (1-exp (-2*s)) := by
      apply sqrt_le_sqrt
      have hh : exp (-2*s) ≤ exp (-t) := exp_le_exp.mpr (by linarith [hs.1])
      linarith
    have he : exp (-2*s) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    have hnonneg : 0 ≤ exp (-2*s)/sqrt (1-exp (-2*s)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      exp (-2*s)/sqrt (1-exp (-2*s)) ≤ 1/l :=
        div_le_div₀ (by positivity) he hl hden
      _ ≤ C := by dsimp [C]; linarith

end
end PersistencePays
#print axioms PersistencePays.hasDerivAt_mehler
