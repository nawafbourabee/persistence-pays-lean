import PersistencePays.StoppedKernel
import PersistencePays.UnadjustedEpochLaw

/-! Exact finite-noise law of the stopped subprobability kernel. -/
noncomputable section
namespace PersistencePays.FiniteNoise
open MeasureTheory ProbabilityTheory Set
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

/-- Every retained step starts in the good state/noise set. -/
def goodBlock (f : S×B → S) (G : Set (S×B)) : (n : ℕ) → S → Set (Fin n → B)
  | 0, _ => univ
  | n+1, s => {b | (fun i => b i.castSucc) ∈ goodBlock f G n s ∧
      (trajectory f n s (fun i => b i.castSucc),b (Fin.last n)) ∈ G}

theorem measurable_goodBlock_joint (f : S×B → S) (hf : Measurable f)
    (G : Set (S×B)) (hG : MeasurableSet G) (n : ℕ) :
    MeasurableSet {p : S×(Fin n → B) | p.2 ∈ goodBlock f G n p.1} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
      change MeasurableSet {p : S×(Fin (n+1) → B) |
        (fun i => p.2 i.castSucc) ∈ goodBlock f G n p.1 ∧
        (trajectory f n p.1 (fun i => p.2 i.castSucc),p.2 (Fin.last n)) ∈ G}
      have hp : Measurable (fun p : S×(Fin (n+1) → B) => (p.1,fun i : Fin n => p.2 i.castSucc)) :=
        measurable_fst.prodMk (measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply i.castSucc).comp measurable_snd)
      exact (hp ih).inter (((measurable_trajectory f hf n).comp hp).prodMk
        ((measurable_pi_apply (Fin.last n)).comp measurable_snd) hG)

theorem measurable_goodBlock (f : S×B → S) (hf : Measurable f)
    (G : Set (S×B)) (hG : MeasurableSet G) (n : ℕ) (s : S) :
    MeasurableSet (goodBlock f G n s) :=
  measurable_prodMk_left (measurable_goodBlock_joint f hf G hG n)

omit [MeasurableSpace S] [MeasurableSpace B] in
theorem goodBlock_snoc (f : S×B → S) (G : Set (S×B)) (n : ℕ) (s : S)
    (b : Fin n → B) (last : B) :
    Fin.snoc b last ∈ goodBlock f G (n+1) s ↔
      b ∈ goodBlock f G n s ∧ (trajectory f n s b,last) ∈ G := by
  simp [goodBlock]

omit [MeasurableSpace S] [MeasurableSpace B] in
theorem goodBlock_iff_all (f : S×B → S) (G : Set (S×B)) (b : ℕ → B) (n : ℕ) (s : S) :
    (fun i : Fin n => b i) ∈ goodBlock f G n s ↔
      ∀ k<n, (trajectory f k s (fun i => b i), b k) ∈ G := by
  induction n with
  | zero => simp [goodBlock]
  | succ n ih =>
      change ((fun i : Fin n => b i) ∈ goodBlock f G n s ∧
        (trajectory f n s (fun i => b i),b n) ∈ G) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hp,hl⟩ k hk
        by_cases hkn : k<n
        · exact hp k hkn
        · have he : k=n := by omega
          subst k
          exact hl
      · intro hp
        exact ⟨fun k hk => hp k (by omega), hp n (by omega)⟩

/-- Restricting the actual finite product noise law to the literal survival
event gives exactly the iterated substochastic transition. -/
theorem stopped_trajectory_law (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S×B → S) (hf : Measurable f) (G : Set (S×B)) (hG : MeasurableSet G)
    (n : ℕ) (s : S) :
    ((Measure.pi (fun _ : Fin n => μ)).restrict (goodBlock f G n s)).map (trajectory f n s) =
      iterateKernel (stoppedNoiseKernel μ f G hG) n s := by
  induction n with
  | zero => simp [goodBlock, trajectory, iterateKernel, Kernel.id_apply]
  | succ n ih =>
      ext A hA
      rw [Measure.map_apply (measurable_trajectory_fixed f hf (n+1) s) hA,
        Measure.restrict_apply ((measurable_trajectory_fixed f hf (n+1) s) hA),
        ← (snoc_preserving μ n).map_eq,
        Measure.map_apply (snoc_preserving μ n).measurable
          (((measurable_trajectory_fixed f hf (n+1) s) hA).inter (measurable_goodBlock f hf G hG (n+1) s)),
        Measure.prod_apply ((snoc_preserving μ n).measurable
          (((measurable_trajectory_fixed f hf (n+1) s) hA).inter (measurable_goodBlock f hf G hG (n+1) s))),
        iterateKernel, Kernel.comp_apply' _ _ _ hA, ← ih,
        lintegral_map (Kernel.measurable_coe _ hA) (measurable_trajectory_fixed f hf n s),
        ← lintegral_indicator (measurable_goodBlock f hf G hG n s)]
      apply lintegral_congr
      intro b
      by_cases hb : b ∈ goodBlock f G n s
      · have hfs : Measurable (fun u : B => f (trajectory f n s b,u)) :=
          hf.comp (f:=fun u : B => (trajectory f n s b,u)) measurable_prodMk_left
        rw [indicator_of_mem hb, stoppedNoiseKernel_apply μ f hf G hG,
          Measure.map_apply hfs hA,
          Measure.restrict_apply (hfs hA)]
        congr 1
        ext u
        simp only [mem_preimage, mem_inter_iff, trajectory_snoc, goodBlock_snoc, hb, true_and, mem_setOf_eq]
      · rw [indicator_of_notMem hb]
        have he : {u : B | Fin.snoc b u ∈ trajectory f (n+1) s ⁻¹' A ∩ goodBlock f G (n+1) s} = ∅ := by
          ext u
          simp [goodBlock_snoc, hb]
        change μ {u : B | Fin.snoc b u ∈ trajectory f (n+1) s ⁻¹' A ∩ goodBlock f G (n+1) s} = _
        rw [he, measure_empty]

end PersistencePays.FiniteNoise
#print axioms PersistencePays.FiniteNoise.stopped_trajectory_law
