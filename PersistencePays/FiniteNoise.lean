import PersistencePays.StageKernels
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite independent noise blocks and sequential Markov transitions

This file proves the law bridge: an explicit finite array of independent noise
draws, consumed by a deterministic recursion, has the same law as iterating the
one-step noise kernel. No Markov or independence property is assumed of the
recursion; independence comes from the finite product measure.
-/

noncomputable section
namespace PersistencePays.FiniteNoise

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def noiseKernel (μ : Measure B) (f : S × B → S) (_hf : Measurable f) : Kernel S S :=
  (Kernel.id ×ₖ Kernel.const S μ).map f

instance noiseKernel_markov (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (hf : Measurable f) : IsMarkovKernel (noiseKernel μ f hf) :=
  Kernel.IsMarkovKernel.map _ hf

theorem noiseKernel_apply (μ : Measure B) [SFinite μ]
    (f : S × B → S) (hf : Measurable f) (s : S) :
    noiseKernel μ f hf s = μ.map (fun b => f (s, b)) := by
  have hs : Measurable (fun b : B => f (s, b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  ext t ht
  rw [noiseKernel, Kernel.map_apply' _ hf _ ht,
    Kernel.id_prod_apply' _ _ (hf ht), Kernel.const_apply,
    Measure.map_apply hs ht]
  rfl

def trajectory (f : S × B → S) : (n : ℕ) → S → (Fin n → B) → S
  | 0, s, _ => s
  | n + 1, s, b => f (trajectory f n s (fun i => b i.castSucc), b (Fin.last n))

theorem measurable_trajectory (f : S × B → S) (hf : Measurable f) (n : ℕ) :
    Measurable (fun p : S × (Fin n → B) => trajectory f n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hb : Measurable (fun p : S × (Fin (n + 1) → B) =>
          (p.1, fun i : Fin n => p.2 i.castSucc)) := by
        exact measurable_fst.prodMk (measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply i.castSucc).comp measurable_snd)
      exact hf.comp ((ih.comp hb).prodMk
        ((measurable_pi_apply (Fin.last n)).comp measurable_snd))

theorem measurable_trajectory_fixed (f : S × B → S) (hf : Measurable f) (n : ℕ) (s : S) :
    Measurable (trajectory f n s) :=
  (measurable_trajectory f hf n).comp (measurable_const.prodMk measurable_id)

theorem snoc_preserving (μ : Measure B) [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (fun p : (Fin n → B) × B => Fin.snoc p.1 p.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  have h := ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => μ) (Fin.last n)).symm).comp
      (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => μ)) (ν := μ))
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv] using h

omit [MeasurableSpace S] [MeasurableSpace B] in
theorem trajectory_snoc (f : S × B → S) (n : ℕ) (s : S) (b : Fin n → B) (last : B) :
    trajectory f (n + 1) s (Fin.snoc b last) = f (trajectory f n s b, last) := by
  simp [trajectory]

theorem trajectory_law (μ : Measure B) [IsProbabilityMeasure μ]
    (f : S × B → S) (hf : Measurable f) (n : ℕ) (s : S) :
    (Measure.pi (fun _ : Fin n => μ)).map (trajectory f n s) =
      iterateKernel (noiseKernel μ f hf) n s := by
  induction n with
  | zero => simp [trajectory, iterateKernel, Kernel.id_apply]
  | succ n ih =>
      rw [← (snoc_preserving μ n).map_eq,
        Measure.map_map (measurable_trajectory_fixed f hf (n + 1) s)
          (snoc_preserving μ n).measurable]
      simp only [Function.comp_def, trajectory_snoc]
      ext t ht
      have hmap : Measurable (fun p : (Fin n → B) × B => f (trajectory f n s p.1, p.2)) :=
        hf.comp (((measurable_trajectory_fixed f hf n s).comp measurable_fst).prodMk measurable_snd)
      rw [Measure.map_apply hmap ht, Measure.prod_apply (hmap ht),
        iterateKernel, Kernel.comp_apply' _ _ _ ht, ← ih,
        lintegral_map (Kernel.measurable_coe _ ht) (measurable_trajectory_fixed f hf n s)]
      apply lintegral_congr
      intro b
      have hb : Measurable (fun u : B => f (trajectory f n s b, u)) :=
        hf.comp (measurable_const.prodMk measurable_id)
      rw [noiseKernel_apply μ f hf,
        Measure.map_apply hb ht]
      rfl

end PersistencePays.FiniteNoise
