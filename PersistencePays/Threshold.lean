import PersistencePays.Verlet

/-!
# Extended-threshold involution

This file establishes the deterministic involution and exact extended-energy
preservation in Lemma 2.3 of `main_9.pdf`. It does not claim that an arbitrary
involution preserves volume, or prove the manuscript's measure-theoretic
invariance conclusion.
-/

namespace PersistencePays

noncomputable section

variable {α : Type*}

def energyIncrement (H : α → ℝ) (T : α → α) (x : α) : ℝ :=
  H (T x) - H x

def thresholdMap (H : α → ℝ) (T : α → α) (z : α × ℝ) : α × ℝ :=
  if energyIncrement H T z.1 < z.2 then
    (T z.1, z.2 - energyIncrement H T z.1)
  else z

theorem involutive_energyIncrement (H : α → ℝ) (T : α → α)
    (hT : Function.Involutive T) (x : α) :
    energyIncrement H T (T x) = -energyIncrement H T x := by
  simp only [energyIncrement, hT x]
  ring

theorem thresholdMap_positive (H : α → ℝ) (T : α → α)
    (z : α × ℝ) (hz : 0 < z.2) : 0 < (thresholdMap H T z).2 := by
  unfold thresholdMap
  split_ifs with h
  · exact sub_pos.mpr h
  · exact hz

theorem thresholdMap_energy (H : α → ℝ) (T : α → α) (z : α × ℝ) :
    H (thresholdMap H T z).1 + (thresholdMap H T z).2 = H z.1 + z.2 := by
  unfold thresholdMap
  split_ifs
  · simp only [energyIncrement]
    ring
  · rfl

theorem thresholdMap_accept_preserved (H : α → ℝ) (T : α → α)
    (hT : Function.Involutive T) (z : α × ℝ) (hz : 0 < z.2)
    (ha : energyIncrement H T z.1 < z.2) :
    energyIncrement H T (thresholdMap H T z).1 < (thresholdMap H T z).2 := by
  simp only [thresholdMap, ite_eq_left ha, involutive_energyIncrement H T hT]
  linarith

theorem thresholdMap_involutive_on_positive (H : α → ℝ) (T : α → α)
    (hT : Function.Involutive T) (z : α × ℝ) (hz : 0 < z.2) :
    thresholdMap H T (thresholdMap H T z) = z := by
  by_cases ha : energyIncrement H T z.1 < z.2
  · have hb := thresholdMap_accept_preserved H T hT z hz ha
    rw [thresholdMap, ite_eq_left hb]
    simp only [thresholdMap, ite_eq_left ha, involutive_energyIncrement H T hT, hT z.1]
    ext <;> simp
  · simp [thresholdMap, ha]

def positiveThresholdMap (H : α → ℝ) (T : α → α)
    (z : {z : α × ℝ // 0 < z.2}) : {z : α × ℝ // 0 < z.2} :=
  ⟨thresholdMap H T z.1, thresholdMap_positive H T z.1 z.2⟩

theorem positiveThresholdMap_involutive (H : α → ℝ) (T : α → α)
    (hT : Function.Involutive T) : Function.Involutive (positiveThresholdMap H T) := by
  intro z
  apply Subtype.ext
  exact thresholdMap_involutive_on_positive H T hT z.1 z.2

def adjustedUpdate (H : α → ℝ) (S Φ : α → α) (z : α × ℝ) : α × ℝ :=
  if energyIncrement H Φ z.1 < z.2 then
    (Φ z.1, z.2 - energyIncrement H Φ z.1)
  else (S z.1, z.2)

/-- Composing the auxiliary involution with velocity reversal gives exactly
the accepted/rejected deterministic branch in Definition 2.2. -/
theorem thresholdMap_adjustedUpdate (H : α → ℝ) (S Φ : α → α)
    (hS : Function.Involutive S) (hH : ∀ x, H (S x) = H x) (z : α × ℝ) :
    (S (thresholdMap H (S ∘ Φ) z).1, (thresholdMap H (S ∘ Φ) z).2) =
      adjustedUpdate H S Φ z := by
  have hd : energyIncrement H (S ∘ Φ) z.1 = energyIncrement H Φ z.1 := by
    simp [energyIncrement, hH]
  unfold thresholdMap adjustedUpdate
  rw [hd]
  split_ifs <;> simp only [Function.comp_apply, hS (Φ z.1)]

section ActualVerlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual extended Verlet proposal in Lemma 2.3 is an involution. -/
theorem verlet_positiveThresholdMap_involutive (U : E → ℝ) (g : E → E) (h : ℝ) :
    Function.Involutive (positiveThresholdMap (phaseEnergy U)
      (fun z => velocityFlip (verlet g h z))) :=
  positiveThresholdMap_involutive _ _ (flipped_verlet_involutive g h)

/-- Its velocity-reversed image is the deterministic accepted/rejected step
in Definition 2.2, before the final OU half-step. -/
theorem verlet_thresholdMap_adjustedUpdate (U : E → ℝ) (g : E → E) (h : ℝ)
    (z : (E × E) × ℝ) :
    (velocityFlip (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).1,
      (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).2) =
      adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h) z :=
  thresholdMap_adjustedUpdate _ _ _ velocityFlip_involutive (phaseEnergy_velocityFlip U) z

end ActualVerlet

end

end PersistencePays

#print axioms PersistencePays.positiveThresholdMap_involutive
#print axioms PersistencePays.thresholdMap_energy
#print axioms PersistencePays.thresholdMap_adjustedUpdate
#print axioms PersistencePays.verlet_positiveThresholdMap_involutive
#print axioms PersistencePays.verlet_thresholdMap_adjustedUpdate
