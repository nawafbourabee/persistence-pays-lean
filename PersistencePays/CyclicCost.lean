import PersistencePays.Rockafellar
import PersistencePays.OptimalPermutation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! From finite permutation optimality to the finite-path form of cyclic monotonicity. -/
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ofFn_zipWith {α β γ : Type*} (f : α → β → γ) {n : ℕ}
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zipWith_cons_cons, ih]

lemma ofFn_snoc {α : Type*} {n : ℕ} (f : Fin n → α) (a : α) :
    List.ofFn (Fin.snoc f a) = List.ofFn f ++ [a] := by
  rw [List.ofFn_succ']
  simp

lemma pathWeight_zip (a z : E × E) (l : List (E × E)) :
    pathWeight a l z.1 = (List.zipWith (fun b c : E × E => ⟪b.2,c.1-b.1⟫)
      (a::l) (l++[z])).sum := by
  induction l generalizing a with
  | nil => simp [pathWeight]
  | cons b l ih => simp only [pathWeight, List.cons_append, List.zipWith_cons_cons, List.sum_cons, ih]

def pathArray (a : E × E) (l : List (E × E)) : Fin (l.length+1) → E × E :=
  Fin.cons a l.get

lemma pathWeight_rotate (a : E × E) (l : List (E × E)) :
    pathWeight a l a.1 = ∑ i : Fin (l.length+1),
      ⟪(pathArray a l i).2,
        (pathArray a l (finRotate (l.length+1) i)).1 - (pathArray a l i).1⟫ := by
  change pathWeight a l a.1 = _
  rw [pathWeight_zip a a l]
  conv_lhs => rw [← List.ofFn_get l]
  unfold pathArray
  have hh := ofFn_zipWith (fun b c : E × E => ⟪b.2,c.1-b.1⟫)
    (@Fin.cons _ (fun _ => E × E) a l.get) (@Fin.snoc _ (fun _ => E × E) l.get a)
  rw [List.ofFn_cons, ofFn_snoc] at hh
  rw [hh, List.sum_ofFn]
  simp only [Fin.snoc_eq_cons_rotate]

lemma rotated_cost_difference {ι : Type*} [Fintype ι]
    (p : ι → E×E) (e : Equiv.Perm ι) :
    (∑ i, ‖(p (e i)).1-(p i).2‖^2) - (∑ i, ‖(p i).1-(p i).2‖^2) =
      -2 * ∑ i, ⟪(p i).2,(p (e i)).1-(p i).1⟫ := by
  have hn (x y : E) : ‖x-y‖^2 = ‖x‖^2 + ‖y‖^2 - 2*⟪y,x⟫ := by
    rw [norm_sub_sq_real, real_inner_comm x y]
    ring
  simp_rw [hn, inner_sub_right, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [Equiv.sum_comp e (fun i => ‖(p i).1‖^2)]
  ring

variable [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

theorem optimal_support_cyclicallyMonotone (μ ν : ProbabilityMeasure E)
    (π : ProbabilityMeasure (E×E)) (hπ : IsOptimal μ ν π)
    (hfinite : squaredCost π ≠ ∞) : CyclicallyMonotone (π : Measure (E×E)).support := by
  intro a ha l hl
  let p : Fin (l.length+1) → E×E := pathArray a l
  let e := finRotate (l.length+1)
  have hp : ∀ i, p i ∈ (π : Measure (E×E)).support := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha
    · exact hl _ (List.get_mem l j)
  have hh := optimal_support_permutation_real μ ν π hπ hfinite e.symm p hp
  have hr : (∑ i, ‖(p i).1-(p (e.symm i)).2‖^2) =
      ∑ i, ‖(p (e i)).1-(p i).2‖^2 := by
    have hx := Equiv.sum_comp e (fun i => ‖(p i).1-(p (e.symm i)).2‖^2)
    simpa only [Equiv.symm_apply_apply] using hx.symm
  rw [hr] at hh
  have hi := rotated_cost_difference p e
  rw [pathWeight_rotate]
  change (∑ i, ⟪(p i).2,(p (e i)).1-(p i).1⟫) ≤ 0
  linarith

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.optimal_support_cyclicallyMonotone
