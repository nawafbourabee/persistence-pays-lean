import Mathlib

/-!
# Deterministic acceptance paths for Definition 2.2

Fixing the Gaussian noise block makes the accepted update, rejected update,
and energy defect deterministic maps indexed by the step.  The results here
prove the pathwise all-acceptance equivalence in Proposition 5.1. They do not
yet prove the statement about the probability of that event.
-/

namespace PersistencePays.EpochAcceptance

variable {α : Type*}

/-- The actual carried-threshold path, including rejections. The first map
is the accepted update (including the two OU draws); the second is the
rejected update with velocity reversal and the same OU draws. -/
noncomputable def adjustedPath (accept reject : ℕ → α → α)
    (defect : ℕ → α → ℝ) (z : α) (ell : ℝ) : ℕ → α × ℝ
  | 0 => (z, ell)
  | n + 1 =>
      let current := adjustedPath accept reject defect z ell n
      if defect n current.1 < current.2 then
        (accept n current.1, current.2 - defect n current.1)
      else (reject n current.1, current.2)

/-- The path obtained by accepting every proposal. -/
def referencePath (accept : ℕ → α → α) (z : α) : ℕ → α
  | 0 => z
  | n + 1 => accept n (referencePath accept z n)

/-- Accumulated energy defects along the all-accepted reference path. -/
noncomputable def accumulatedWork (accept : ℕ → α → α)
    (defect : ℕ → α → ℝ) (z : α) : ℕ → ℝ
  | 0 => 0
  | n + 1 => accumulatedWork accept defect z n + defect n (referencePath accept z n)

/-- Every proposal at an actual step before `n` is accepted. -/
def allAccepted (accept reject : ℕ → α → α)
    (defect : ℕ → α → ℝ) (z : α) (ell : ℝ) : ℕ → Prop
  | 0 => True
  | n + 1 => allAccepted accept reject defect z ell n ∧
      defect n (adjustedPath accept reject defect z ell n).1 <
        (adjustedPath accept reject defect z ell n).2

/-- Along an all-accepted prefix, the actual state is the reference state
and the threshold is its initial value minus the accumulated work. -/
theorem adjustedPath_eq_reference_of_allAccepted
    (accept reject : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (ell : ℝ) (n : ℕ)
    (ha : allAccepted accept reject defect z ell n) :
    adjustedPath accept reject defect z ell n =
      (referencePath accept z n, ell - accumulatedWork accept defect z n) := by
  induction n with
  | zero => simp [adjustedPath, referencePath, accumulatedWork]
  | succ n ih =>
      have hp := ih ha.1
      have ht := ha.2
      simp only [adjustedPath]
      rw [ite_eq_left ht, hp]
      simp only [referencePath, accumulatedWork, Prod.mk.injEq]
      constructor
      · trivial
      · ring

/-- Exact pathwise form of Proposition 5.1. Only work along the unadjusted
reference path appears on the right, even though the left uses the actual
path with possible rejections. -/
theorem allAccepted_iff_partialWork
    (accept reject : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (ell : ℝ) (n : ℕ) :
    allAccepted accept reject defect z ell n ↔
      ∀ k < n, accumulatedWork accept defect z (k + 1) < ell := by
  induction n with
  | zero => simp [allAccepted]
  | succ n ih =>
      constructor
      · intro ha k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hkEq
        · exact ih.mp ha.1 k hk
        · subst k
          have hp := adjustedPath_eq_reference_of_allAccepted
            accept reject defect z ell n ha.1
          have ht := ha.2
          rw [hp] at ht
          simp only [accumulatedWork] at ht ⊢
          linarith
      · intro hb
        have ha : allAccepted accept reject defect z ell n :=
          ih.mpr (fun k hk => hb k (Nat.lt_succ_of_lt hk))
        refine ⟨ha, ?_⟩
        have hp := adjustedPath_eq_reference_of_allAccepted
          accept reject defect z ell n ha
        rw [hp]
        have ht := hb n (Nat.lt_succ_self n)
        simp only [accumulatedWork] at ht ⊢
        linarith

/-- Equivalent indexing by nonempty prefixes `1 <= j <= n`. -/
theorem allAccepted_iff_prefixWork
    (accept reject : ℕ → α → α) (defect : ℕ → α → ℝ)
    (z : α) (ell : ℝ) (n : ℕ) :
    allAccepted accept reject defect z ell n ↔
      ∀ j, 1 ≤ j → j ≤ n → accumulatedWork accept defect z j < ell := by
  rw [allAccepted_iff_partialWork]
  constructor
  · intro h j hj hjn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact h k (by omega)
  · intro h k hk
    exact h (k + 1) (by omega) (by omega)

/-- The accumulated work is the usual finite sum of reference defects. -/
theorem accumulatedWork_eq_sum
    (accept : ℕ → α → α) (defect : ℕ → α → ℝ) (z : α) (n : ℕ) :
    accumulatedWork accept defect z n =
      ∑ k ∈ Finset.range n, defect k (referencePath accept z k) := by
  induction n with
  | zero => simp [accumulatedWork]
  | succ n ih => simp [accumulatedWork, Finset.sum_range_succ, ih]

/-- The leading position-only defect telescopes along every reference path.
The hypothesis is the energy identity proved separately for Verlet. -/
theorem accumulatedWork_telescope
    (accept : ℕ → α → α) (defect remainder : ℕ → α → ℝ)
    (G : α → ℝ) (z : α)
    (hdefect : ∀ k x, defect k x = G (accept k x) - G x + remainder k x)
    (n : ℕ) :
    accumulatedWork accept defect z n =
      G (referencePath accept z n) - G z +
        ∑ k ∈ Finset.range n, remainder k (referencePath accept z k) := by
  induction n with
  | zero => simp [accumulatedWork, referencePath]
  | succ n ih =>
      rw [accumulatedWork, ih, hdefect, Finset.sum_range_succ, referencePath]
      ring

/-- Nonnegativity of the leading corrector gives the signed accumulated
defect bound used to control rejection in Proposition 5.1. -/
theorem accumulatedWork_le_corrector_add_abs_remainder
    (accept : ℕ → α → α) (defect remainder : ℕ → α → ℝ)
    (G : α → ℝ) (z : α)
    (hdefect : ∀ k x, defect k x = G (accept k x) - G x + remainder k x)
    (hG : 0 ≤ G z) (n : ℕ) :
    accumulatedWork accept defect z n ≤ G (referencePath accept z n) +
      ∑ k ∈ Finset.range n, |remainder k (referencePath accept z k)| := by
  rw [accumulatedWork_telescope accept defect remainder G z hdefect n]
  have hs : (∑ k ∈ Finset.range n, remainder k (referencePath accept z k)) ≤
      ∑ k ∈ Finset.range n, |remainder k (referencePath accept z k)| :=
    Finset.sum_le_sum (fun k _ => le_abs_self _)
  linarith

/-- Bounds for each prefix of the reference path suffice for acceptance
of the actual path. No assertion about the law of the noise is needed. -/
theorem allAccepted_of_corrector_remainder_bound
    (accept reject : ℕ → α → α) (defect remainder : ℕ → α → ℝ)
    (G : α → ℝ) (z : α) (ell : ℝ)
    (hdefect : ∀ k x, defect k x = G (accept k x) - G x + remainder k x)
    (hG : 0 ≤ G z) (n : ℕ)
    (hb : ∀ k < n, G (referencePath accept z (k + 1)) +
      (∑ j ∈ Finset.range (k + 1), |remainder j (referencePath accept z j)|) < ell) :
    allAccepted accept reject defect z ell n := by
  rw [allAccepted_iff_partialWork]
  intro k hk
  exact lt_of_le_of_lt
    (accumulatedWork_le_corrector_add_abs_remainder
      accept defect remainder G z hdefect hG (k + 1)) (hb k hk)

end PersistencePays.EpochAcceptance
