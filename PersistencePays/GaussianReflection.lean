import PersistencePays.GaussianOU
import PersistencePays.GaussianBridgeLaw
import PersistencePays.TransportDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The joint Gaussian reflection which identifies the adjoint Mehler action
with the density of the actual OU-updated probability law. -/
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianReflection (r σ : ℝ) (z : E × E) : E × E :=
  (r • z.1 + σ • z.2, σ • z.1 - r • z.2)

lemma gaussianReflection_involutive (r σ : ℝ) (hn : r^2+σ^2=1) :
    Function.Involutive (gaussianReflection (E := E) r σ) := by
  intro z
  ext <;> dsimp [gaussianReflection]
  · calc
      _ = (r^2+σ^2) • z.1 := by module
      _ = z.1 := by rw [hn, one_smul]
  · calc
      _ = (r^2+σ^2) • z.2 := by module
      _ = z.2 := by rw [hn, one_smul]

def gaussianReflectionEquiv (r σ : ℝ) (hn : r^2+σ^2=1) : (E × E) ≃ᵐ (E × E) where
  toEquiv := {
    toFun := gaussianReflection r σ
    invFun := gaussianReflection r σ
    left_inv := gaussianReflection_involutive r σ hn
    right_inv := gaussianReflection_involutive r σ hn }
  measurable_toFun := by change Measurable (gaussianReflection r σ); unfold gaussianReflection; fun_prop
  measurable_invFun := by change Measurable (gaussianReflection r σ); unfold gaussianReflection; fun_prop

lemma gaussianReflection_preserving (r σ : ℝ) (hn : r^2+σ^2=1) (hσ : 0 ≤ σ) :
    MeasurePreserving (gaussianReflection (E := E) r σ)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  have hr1 : -1 ≤ r := by nlinarith [sq_nonneg σ]
  have hr2 : r ≤ 1 := by nlinarith [sq_nonneg σ]
  have hs : sqrt (1-r^2) = σ := by
    rw [show 1-r^2=σ^2 by linarith, sqrt_sq_eq_abs, abs_of_nonneg hσ]
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation (arccos r) : E × E →L[ℝ] E × E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
    ⟨by fun_prop, IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero
      (fun L => integral_strongDual_stdGaussian L) _⟩
  have hneg : MeasurePreserving (fun y : E => -y) (stdGaussian E) (stdGaussian E) :=
    ⟨by fun_prop, stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  have hneg2 := (MeasurePreserving.id (stdGaussian E)).prod hneg
  convert hneg2.comp hrot using 1
  ext z <;> simp only [Function.comp_apply, gaussianReflection,
    ContinuousLinearMap.rotation_apply, cos_arccos hr1 hr2, sin_arccos,
    Prod.map_apply, id_eq]
  · rw [hs]
  · rw [hs]
    simp only [neg_smul, neg_add_rev, neg_neg, sub_eq_add_neg]
    abel

def gaussianUpdate (r σ : ℝ) (μ : Measure E) : Measure E :=
  (μ.prod (stdGaussian E)).map (gaussianOU r σ)

/-- Detailed balance at the level of actual densities. The integral on the
right is the adjoint Mehler average, and no moments of the input law are used. -/
theorem gaussianUpdate_density (r σ : ℝ) (hn : r^2+σ^2=1) (hσ : 0 ≤ σ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    gaussianUpdate r σ ((stdGaussian E).withDensity f) =
      (stdGaussian E).withDensity
        (fun x => ∫⁻ y, f (r • x + σ • y) ∂stdGaussian E) := by
  let e := gaussianReflectionEquiv (E := E) r σ hn
  have hm : (((stdGaussian E).prod (stdGaussian E)).withDensity (fun z => f z.1)).map e =
      ((stdGaussian E).prod (stdGaussian E)).withDensity
        (fun z => f (r • z.1 + σ • z.2)) := by
    have hfm : Measurable (fun z : E × E => f z.1) := hf.comp measurable_fst
    rw [map_density_equiv e _ _ hfm]
    have he : (((stdGaussian E).prod (stdGaussian E)).map e) =
        (stdGaussian E).prod (stdGaussian E) := (gaussianReflection_preserving r σ hn hσ).map_eq
    rw [he]
    rfl
  have hfst := congrArg Measure.fst hm
  rw [fst_withDensity_prod _ _ _ (by fun_prop)] at hfst
  rw [← prod_withDensity_left hf] at hfst
  rw [Measure.fst_map_prodMk (by unfold e gaussianReflectionEquiv gaussianReflection; fun_prop)] at hfst
  exact hfst

end
end PersistencePays
#print axioms PersistencePays.gaussianReflection_preserving
#print axioms PersistencePays.gaussianUpdate_density
