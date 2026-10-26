import PersistencePays.GaussianOU

/-! Finite normalized sums of independent standard Gaussian vectors. -/

noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Arbitrary finite real weights with squared norm one preserve the standard
Gaussian law when applied to independent standard Gaussian vectors. -/
theorem gaussian_weighted_sum_preserving {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    MeasurePreserving (fun x : ι → E => ∑ i, a i • x i)
      (Measure.pi (fun _ : ι => stdGaussian E)) (stdGaussian E) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_charFun
  have hi : iIndepFun (fun i (x : ι → E) => a i • x i)
      (Measure.pi (fun _ : ι => stdGaussian E)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hmX : ∀ i, AEMeasurable (fun x : ι → E => a i • x i)
      (Measure.pi (fun _ : ι => stdGaussian E)) := fun i =>
    ((measurable_pi_apply i).const_smul (a i)).aemeasurable
  rw [hi.charFun_map_fun_sum_eq_prod hmX]
  funext t
  simp only [Finset.prod_apply]
  have hm (i : ι) : (Measure.pi (fun _ : ι => stdGaussian E)).map
      (fun x => a i • x i) = (stdGaussian E).map (fun x => a i • x) := by
    conv_rhs => rw [← (measurePreserving_eval
      (fun _ : ι => stdGaussian E) i).map_eq]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  simp_rw [hm, charFun_map_smul, charFun_stdGaussian]
  rw [← Complex.exp_sum]
  congr 1
  have hn (i : ι) : (‖a i • t‖ : ℂ) ^ 2 =
      (a i : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast (show ‖a i • t‖ ^ 2 = a i ^ 2 * ‖t‖ ^ 2 by
      simp [norm_smul, mul_pow, sq_abs])
  simp_rw [hn]
  have hc : ∑ i, (a i : ℂ) ^ 2 = 1 := by exact_mod_cast ha
  calc
    ∑ i, -((a i : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2) / 2 =
        ∑ i, (a i : ℂ) ^ 2 * (-(‖t‖ : ℂ) ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (a i : ℂ) ^ 2) * (-(‖t‖ : ℂ) ^ 2 / 2) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hc]; ring

/-- The normalized sum of `n` independent standard Gaussian vectors. -/
theorem gaussian_normalized_sum_preserving (n : ℕ) (hn : 0 < n) :
    MeasurePreserving
      (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
      (Measure.pi (fun _ : Fin n => stdGaussian E)) (stdGaussian E) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  have ha : ∑ _ : Fin n, ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [inv_pow, hs, mul_inv_cancel₀ (ne_of_gt hn')]
  simpa only [Finset.smul_sum] using
    (gaussian_weighted_sum_preserving (E := E)
      (fun _ : Fin n => (Real.sqrt (n : ℝ))⁻¹) ha)

/-- A normalized sum over any nonempty set of coordinates has the same law;
the unused coordinates remain in the original product probability space. -/
theorem gaussian_normalized_finset_sum_preserving {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) :
    MeasurePreserving
      (fun x : ι → E => (Real.sqrt (s.card : ℝ))⁻¹ • ∑ i ∈ s, x i)
      (Measure.pi (fun _ : ι => stdGaussian E)) (stdGaussian E) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsq : Real.sqrt (s.card : ℝ) ^ 2 = s.card := Real.sq_sqrt hc.le
  let a : ι → ℝ := fun i => if i ∈ s then (Real.sqrt (s.card : ℝ))⁻¹ else 0
  have ha : ∑ i, a i ^ 2 = 1 := by
    simp only [a, ite_pow, zero_pow (by decide : 2 ≠ 0)]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [inv_pow, hsq, mul_inv_cancel₀ (ne_of_gt hc)]
  have hf : (fun x : ι → E => ∑ i, a i • x i) =
      (fun x : ι → E => (Real.sqrt (s.card : ℝ))⁻¹ • ∑ i ∈ s, x i) := by
    funext x
    simp [a, Finset.smul_sum]
  rw [← hf]
  exact gaussian_weighted_sum_preserving a ha

/-- Removing one coordinate from at least two independent Gaussian blocks
and normalizing the remaining sum still gives a standard Gaussian. -/
theorem gaussian_normalized_erased_sum_preserving (n : ℕ) (hn : 1 < n)
    (i : Fin n) :
    MeasurePreserving
      (fun x : Fin n → E => (Real.sqrt ((n - 1 : ℕ) : ℝ))⁻¹ •
        ∑ j ∈ Finset.univ.erase i, x j)
      (Measure.pi (fun _ : Fin n => stdGaussian E)) (stdGaussian E) := by
  have hc : (Finset.univ.erase i).card = n - 1 := by simp
  have hs : (Finset.univ.erase i).Nonempty := by
    rw [← Finset.card_pos, hc]
    omega
  simpa only [hc] using gaussian_normalized_finset_sum_preserving
    (E := E) (Finset.univ.erase i) hs

end PersistencePays

#print axioms PersistencePays.gaussian_weighted_sum_preserving
#print axioms PersistencePays.gaussian_normalized_sum_preserving
#print axioms PersistencePays.gaussian_normalized_erased_sum_preserving
