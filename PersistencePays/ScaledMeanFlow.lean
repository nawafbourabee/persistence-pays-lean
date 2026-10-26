import PersistencePays.BoundedMeanFlow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A linear growth field becomes bounded after removing its scalar dilation.
This yields actual trajectories on any fixed finite interval. -/
noncomputable section
namespace PersistencePays
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rescaled_field_lipschitz {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {c : ℝ} (hc : 0<c) : LipschitzWith K (fun x => c⁻¹ • F (c • x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_smul₀,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  calc
    _ ≤ c⁻¹*((K:ℝ)*dist (c•x) (c•y)) :=
      mul_le_mul_of_nonneg_left (hF.dist_le_mul _ _) (inv_nonneg.mpr hc.le)
    _ = _ := by
      rw [dist_smul₀,Real.norm_of_nonneg hc.le]
      field_simp

theorem rescaled_field_bound {F : E → E} {B c : ℝ} (hc : 1≤c)
    (hF : ∀ x, ‖F x‖ ≤ B) (x : E) : ‖c⁻¹ • F (c•x)‖ ≤ B := by
  have hc0 : 0<c := by linarith
  have hB : 0≤B := (norm_nonneg (F (c•x))).trans (hF _)
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc0.le)]
  have hi : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  calc
    _ ≤ c⁻¹*B := mul_le_mul_of_nonneg_left (hF _) (inv_nonneg.mpr hc0.le)
    _ ≤ B := by nlinarith

theorem dilated_bounded_field_trajectory {bfield : ℝ → E → E} {c β : ℝ → ℝ}
    {a b : ℝ} (τ : Icc a b) (B K : ℝ≥0)
    (hc : Continuous c) (hc1 : ∀ s, 1≤c s)
    (hcd : ∀ s, HasDerivAt c (β s*c s) s)
    (hb : Continuous bfield.uncurry)
    (hl : ∀ s ∈ Icc a b, LipschitzWith K (bfield s))
    (hbound : ∀ s ∈ Icc a b, ∀ x, ‖bfield s x‖ ≤ B) (x : E) :
    ∃ X : ℝ → E, X τ=x ∧ ∀ s ∈ Icc a b,
      HasDerivWithinAt X (β s • X s+bfield s (X s)) (Icc a b) s := by
  let f : ℝ → E → E := fun s y => (c s)⁻¹ • bfield s (c s • y)
  have hc0 (s:ℝ) : 0<c s := by linarith [hc1 s]
  have hf : Continuous f.uncurry := by
    exact (hc.inv₀ (fun s => (hc0 s).ne')).comp continuous_fst |>.smul
      (hb.comp (continuous_fst.prodMk ((hc.comp continuous_fst).smul continuous_snd)))
  have hfl (s:ℝ) (hs:s∈Icc a b) : LipschitzWith K (f s) :=
    rescaled_field_lipschitz (hl s hs) (hc0 s)
  have hfb (s:ℝ) (hs:s∈Icc a b) (y:E) : ‖f s y‖≤B :=
    rescaled_field_bound (hc1 s) (hbound s hs) y
  obtain ⟨Y,hY,hYd⟩ := bounded_field_trajectory τ B K hf hfl hfb ((c τ)⁻¹ • x)
  refine ⟨fun s => c s • Y s,?_,?_⟩
  · change c τ • Y τ = x
    rw [hY,smul_smul,mul_inv_cancel₀ (hc0 τ).ne',one_smul]
  · intro s hs
    have hd := (hcd s).hasDerivWithinAt.smul (hYd s hs)
    convert hd using 1
    · rfl
    · simp [f,smul_smul,mul_inv_cancel₀ (hc0 s).ne',add_comm]

end PersistencePays
#print axioms PersistencePays.dilated_bounded_field_trajectory
