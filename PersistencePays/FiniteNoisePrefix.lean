import PersistencePays.StoppedNoiseLaw

noncomputable section
namespace PersistencePays.FiniteNoise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def prefixNoise {k n : ℕ} (h : k ≤ n) (b : Fin n → B) : Fin k → B :=
  fun i => b (Fin.castLE h i)

theorem prefixNoise_preserving (μ : Measure B) [IsProbabilityMeasure μ]
    {k n : ℕ} (h : k ≤ n) :
    MeasurePreserving (prefixNoise (B:=B) h) (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Fin k => μ)) := by
  induction n with
  | zero =>
      have hk : k=0 := by omega
      subst k
      change MeasurePreserving id _ _
      exact MeasurePreserving.id _
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have ht : MeasurePreserving (fun b : Fin (n+1) → B => fun i : Fin n => b i.castSucc)
            (Measure.pi (fun _ : Fin (n+1) => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
          convert (measurePreserving_snd (μ:=μ) (ν:=Measure.pi (fun _ : Fin n => μ))).comp
              (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) (Fin.last n)) using 1
          funext b i
          change b i.castSucc = b ((Fin.last n).succAbove i)
          rw [Fin.succAbove_last]
        exact (ih hkn).comp ht
      · have hk : k=n+1 := by omega
        subst k
        change MeasurePreserving id _ _
        exact MeasurePreserving.id _


omit [MeasurableSpace S] [MeasurableSpace B] in
theorem goodBlock_prefix (f : S×B → S) (G : Set (S×B)) {k n : ℕ}
    (h : k ≤ n) (s : S) (b : Fin n → B) (hb : b ∈ goodBlock f G n s) :
    prefixNoise h b ∈ goodBlock f G k s := by
  induction n with
  | zero =>
      have hk : k=0 := by omega
      subst k
      exact hb
  | succ n ih =>
      by_cases hkn : k ≤ n
      · exact ih hkn (fun i => b i.castSucc) hb.1
      · have hk : k=n+1 := by omega
        subst k
        exact hb

theorem stopped_prefix_event_measure (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S×B → S) (hf : Measurable f) (G : Set (S×B)) (hG : MeasurableSet G)
    {k n : ℕ} (h : k ≤ n) (s : S) (A : Set S) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => μ))
      {b | prefixNoise h b ∈ goodBlock f G k s ∧ trajectory f k s (prefixNoise h b) ∈ A} =
      iterateKernel (stoppedNoiseKernel μ f G hG) k s A := by
  rw [← stopped_trajectory_law μ f hf G hG k s,
    Measure.map_apply (measurable_trajectory_fixed f hf k s) hA,
    Measure.restrict_apply ((measurable_trajectory_fixed f hf k s) hA),
    ← (prefixNoise_preserving μ h).map_eq,
    Measure.map_apply (prefixNoise_preserving μ h).measurable
      (((measurable_trajectory_fixed f hf k s) hA).inter (measurable_goodBlock f hf G hG k s))]
  congr 1
  ext b
  simp only [mem_setOf_eq, mem_preimage, mem_inter_iff, and_comm]


/-- A finite maximal-event bound on one genuine finite product probability space. -/
theorem stopped_maximal_event_bound (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S×B → S) (hf : Measurable f) (G : Set (S×B)) (hG : MeasurableSet G)
    (n : ℕ) (s : S) (A : Set S) (hA : MeasurableSet A) (q : ℝ≥0∞)
    (hq : ∀ k≤n, iterateKernel (stoppedNoiseKernel μ f G hG) k s A ≤ q) :
    (Measure.pi (fun _ : Fin n => μ))
      {b | ∃ k : Fin (n+1), trajectory f k s (prefixNoise (Nat.le_of_lt_succ k.isLt) b) ∈ A} ≤
      (Measure.pi (fun _ : Fin n => μ)) (goodBlock f G n s)ᶜ + (n+1 : ℝ≥0∞)*q := by
  let C : Fin (n+1) → Set (Fin n → B) := fun k =>
    {b | prefixNoise (Nat.le_of_lt_succ k.isLt) b ∈ goodBlock f G k s ∧
      trajectory f k s (prefixNoise (Nat.le_of_lt_succ k.isLt) b) ∈ A}
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => μ)) ((goodBlock f G n s)ᶜ ∪ ⋃ k, C k) := by
      apply measure_mono
      rintro b ⟨k,hk⟩
      by_cases hb : b ∈ goodBlock f G n s
      · exact Or.inr (mem_iUnion.mpr ⟨k, goodBlock_prefix f G _ s b hb, hk⟩)
      · exact Or.inl hb
    _ ≤ (Measure.pi (fun _ : Fin n => μ)) (goodBlock f G n s)ᶜ +
        ∑' k, (Measure.pi (fun _ : Fin n => μ)) (C k) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑' _ : Fin (n+1), q := by
          apply ENNReal.tsum_le_tsum
          intro k
          exact (stopped_prefix_event_measure μ f hf G hG _ s A hA).le.trans
            (hq k (Nat.le_of_lt_succ k.isLt))
        _ = _ := by simp [tsum_fintype, Nat.cast_add, Nat.cast_one]

end PersistencePays.FiniteNoise
