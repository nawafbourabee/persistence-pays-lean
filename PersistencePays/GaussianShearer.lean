import PersistencePays.GaussianFunctionalEntropy
import PersistencePays.GaussianFiniteSum
import PersistencePays.EntropyShearer

/-! Exact OU entropy contraction at squared correlation `(n-1)/n`, obtained
by tensorization of an exchangeable Gaussian ridge density. -/
open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open scoped ENNReal BigOperators
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_ridge_conditional (n : ℕ) (hn : 1 < n) (i : Fin n) (f : E → ℝ) :
    condExpExceptCoord (μs := fun _ : Fin n => stdGaussian E) i
      (fun x => f ((sqrt (n : ℝ))⁻¹ • ∑ j : Fin n, x j)) =
    (fun x => gaussianAverage (sqrt ((n-1 : ℕ) : ℝ) / sqrt (n : ℝ))
      ((sqrt (n : ℝ))⁻¹) f
      ((sqrt ((n-1 : ℕ) : ℝ))⁻¹ • ∑ j ∈ Finset.univ.erase i, x j)) := by
  classical
  have hn1 : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hs : sqrt ((n-1 : ℕ) : ℝ) ≠ 0 := (sqrt_pos.2 hn1).ne'
  funext x
  unfold condExpExceptCoord gaussianAverage
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  congr 1
  have hsum : (∑ j : Fin n, Function.update x i y j) =
      (∑ j ∈ Finset.univ.erase i, x j) + y := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  rw [hsum, smul_add, smul_smul]
  congr 1
  congr 1
  field_simp

theorem gaussianAverage_shearer (n : ℕ) (hn : 1 < n) (f : E → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable f (stdGaussian E))
    (hl : Integrable (fun x => f x * log (f x)) (stdGaussian E)) :
    let r := sqrt ((n-1 : ℕ) : ℝ) / sqrt (n : ℝ)
    let σ := (sqrt (n : ℝ))⁻¹
    Integrable (fun x => gaussianAverage r σ f x * log (gaussianAverage r σ f x)) (stdGaussian E) ∧
    LogSobolev.entropy (stdGaussian E) (gaussianAverage r σ f) ≤
      (((n : ℝ)-1)/(n : ℝ))*LogSobolev.entropy (stdGaussian E) f := by
  let R : (Fin n → E) → E := fun x => (sqrt (n : ℝ))⁻¹ • ∑ i, x i
  let S : Fin n → (Fin n → E) → E := fun i x =>
    (sqrt ((n-1 : ℕ) : ℝ))⁻¹ • ∑ j ∈ Finset.univ.erase i, x j
  let F := f ∘ R
  let r := sqrt ((n-1 : ℕ) : ℝ) / sqrt (n : ℝ)
  let σ := (sqrt (n : ℝ))⁻¹
  let g := gaussianAverage r σ f
  have hR : MeasurePreserving R (Measure.pi (fun _ : Fin n => stdGaussian E)) (stdGaussian E) :=
    gaussian_normalized_sum_preserving n (by omega)
  have hS (i : Fin n) : MeasurePreserving (S i)
      (Measure.pi (fun _ : Fin n => stdGaussian E)) (stdGaussian E) :=
    gaussian_normalized_erased_sum_preserving n hn i
  have hFm : Measurable F := hf.comp hR.measurable
  have hFi : Integrable F (Measure.pi (fun _ : Fin n => stdGaussian E)) :=
    hR.integrable_comp_of_integrable hi
  have hFl : Integrable (fun x => F x * log (F x))
      (Measure.pi (fun _ : Fin n => stdGaussian E)) := hR.integrable_comp_of_integrable hl
  have hF0 : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => stdGaussian E)] F :=
    Eventually.of_forall (fun x => hf0 _)
  have hgm : Measurable g := measurable_gaussianAverage r σ f hf
  have heq (i : Fin n) : condExpExceptCoord (μs := fun _ : Fin n => stdGaussian E) i F =
      g ∘ S i := gaussian_ridge_conditional n hn i f
  have he (i : Fin n) : LogSobolev.entropy (Measure.pi (fun _ : Fin n => stdGaussian E))
      (condExpExceptCoord (μs := fun _ : Fin n => stdGaussian E) i F) =
      LogSobolev.entropy (stdGaussian E) g := by
    rw [heq]
    exact entropy_comp_measurePreserving (hS i) g hgm
  constructor
  · let i : Fin n := ⟨0, by omega⟩
    have hh := SubAddEnt.condExpExceptCoord_mul_log_integrable i F hFm hF0 hFi hFl
    rw [heq i] at hh
    exact ((hS i).integrable_comp (show AEStronglyMeasurable (fun x => g x * log (g x))
      (stdGaussian E) by fun_prop)).1 hh
  · have hh := entropy_symmetric_leave_one_out F hFm hF0 hFi hFl he (by omega)
    rw [entropy_comp_measurePreserving hR f hf] at hh
    exact hh

end
end PersistencePays
#print axioms PersistencePays.gaussianAverage_shearer
