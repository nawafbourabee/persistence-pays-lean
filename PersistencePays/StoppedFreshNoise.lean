import PersistencePays.FiniteNoisePrefix

/-! The next independent draw after a stopped finite trajectory. -/
noncomputable section
namespace PersistencePays.FiniteNoise
open MeasureTheory ProbabilityTheory Set
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def beforeLastStep (f : S×B → S) (n : ℕ) (s : S) (b : Fin (n+1) → B) : S×B :=
  (trajectory f n s (fun i => b i.castSucc), b (Fin.last n))

theorem measurable_beforeLastStep (f : S×B → S) (hf : Measurable f) (n : ℕ) (s : S) :
    Measurable (beforeLastStep f n s) :=
  ((measurable_trajectory_fixed f hf n s).comp
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc)).prodMk
      (measurable_pi_apply (Fin.last n))

theorem stopped_fresh_noise_law (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S×B → S) (hf : Measurable f) (G : Set (S×B)) (hG : MeasurableSet G)
    (n : ℕ) (s : S) :
    ((Measure.pi (fun _ : Fin (n+1) => μ)).restrict
      {b | (fun i => b i.castSucc) ∈ goodBlock f G n s}).map (beforeLastStep f n s) =
      (iterateKernel (stoppedNoiseKernel μ f G hG) n s).prod μ := by
  have hP : MeasurableSet {b : Fin (n+1) → B | (fun i => b i.castSucc) ∈ goodBlock f G n s} :=
    (measurable_goodBlock f hf G hG n s).preimage
      (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc)
  rw [← (snoc_preserving μ n).map_eq,
    Measure.restrict_map (snoc_preserving μ n).measurable hP,
    Measure.map_map (measurable_beforeLastStep f hf n s) (snoc_preserving μ n).measurable]
  have he : (fun p : (Fin n → B)×B => Fin.snoc p.1 p.2) ⁻¹'
      {b : Fin (n+1) → B | (fun i => b i.castSucc) ∈ goodBlock f G n s} =
        goodBlock f G n s ×ˢ (univ : Set B) := by
    ext p
    simp
  rw [he, ← Measure.restrict_prod_eq_prod_univ]
  have hfun : beforeLastStep f n s ∘ (fun p : (Fin n → B)×B => Fin.snoc p.1 p.2) =
      Prod.map (trajectory f n s) id := by
    funext p
    simp [beforeLastStep, Function.comp_def, Prod.map]
  rw [hfun, ← Measure.map_prod_map _ _ (measurable_trajectory_fixed f hf n s) measurable_id,
    Measure.map_id, stopped_trajectory_law μ f hf G hG n s]

theorem stopped_fresh_noise_law_next (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S×B → S) (hf : Measurable f) (G : Set (S×B)) (hG : MeasurableSet G)
    (n : ℕ) (s : S) :
    ((Measure.pi (fun _ : Fin (n+1) => μ)).restrict (goodBlock f G (n+1) s)).map
      (beforeLastStep f n s) =
      ((iterateKernel (stoppedNoiseKernel μ f G hG) n s).prod μ).restrict G := by
  rw [← stopped_fresh_noise_law μ f hf G hG n s,
    Measure.restrict_map (measurable_beforeLastStep f hf n s) hG,
    Measure.restrict_restrict ((measurable_beforeLastStep f hf n s) hG)]
  congr 2
  ext b
  simp [goodBlock, beforeLastStep, and_comm]

end PersistencePays.FiniteNoise
#print axioms PersistencePays.FiniteNoise.stopped_fresh_noise_law_next
