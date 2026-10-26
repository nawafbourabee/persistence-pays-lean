import PersistencePays.LyapunovBounds
import PersistencePays.ThresholdMeasure

/-! Lemma 5.7: the actual speed-limited comparison map, its inverse, volume law,
and modified-energy growth. -/
namespace PersistencePays
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reverse only velocities above the comparison radius. -/
def speedFlip (vstar : ℝ) (z : E × E) : E × E :=
  if vstar < ‖z.2‖ then velocityFlip z else z

/-- The actual comparison Hamiltonian stage. -/
def comparisonVerlet (g : E → E) (h vstar : ℝ) (z : E × E) : E × E :=
  if ‖flightVelocity g h z‖ ≤ vstar then verlet g h z else velocityFlip z

def comparisonDefect (U : E → ℝ) (g : E → E) (h vstar : ℝ) (z : E × E) : ℝ :=
  if ‖flightVelocity g h z‖ ≤ vstar then
    trapezoidDefect U g z.1 (verlet g h z).1 else 0

theorem speedFlip_involutive (vstar : ℝ) : Function.Involutive (speedFlip (E := E) vstar) := by
  intro z
  by_cases hz : vstar < ‖z.2‖
  · simp [speedFlip, hz, velocityFlip]
  · simp [speedFlip, hz]

theorem speedFlip_measurePreserving (vstar : ℝ) :
    MeasurePreserving (speedFlip (E := E) vstar) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := by
  have hs : MeasurableSet {z : E×E | vstar < ‖z.2‖} :=
    measurableSet_lt measurable_const measurable_snd.norm
  have he : velocityFlip ⁻¹' {z : E×E | vstar < ‖z.2‖} = {z : E×E | vstar < ‖z.2‖} := by
    ext z
    simp [velocityFlip]
  exact preserving_piecewise_id _ _ velocityFlip_measurePreserving _ hs he

theorem comparisonVerlet_factorization (g : E → E) (h vstar : ℝ) (z : E × E) :
    comparisonVerlet g h vstar z =
      kick g (h/2) (drift (h/2) (speedFlip vstar (drift (h/2) (kick g (h/2) z)))) := by
  by_cases hz : ‖flightVelocity g h z‖ ≤ vstar
  · simp only [comparisonVerlet, hz, ite_true]
    have hn : ¬ vstar < ‖(drift (h/2) (kick g (h/2) z)).2‖ := not_lt.mpr hz
    simp only [speedFlip, hn, ite_false, verlet]
    congr 1
    ext <;> simp only [drift]
    module
  · have hy : vstar < ‖(drift (h/2) (kick g (h/2) z)).2‖ := lt_of_not_ge hz
    simp only [comparisonVerlet, hz, ite_false, speedFlip, hy, ite_true]
    ext <;> simp only [kick, drift, velocityFlip]
    · module
    · have hx : z.1 + (h/2)•(z.2-(h/2)•g z.1) +
        (h/2)•(-(z.2-(h/2)•g z.1)) = z.1 := by module
      rw [hx]
      module

theorem comparisonVerlet_inverse (g : E → E) (h vstar : ℝ) (z : E × E) :
    comparisonVerlet g (-h) vstar (comparisonVerlet g h vstar z) = z := by
  simp only [comparisonVerlet_factorization, neg_div, kick_inverse, drift_inverse]
  rw [speedFlip_involutive vstar _]
  simp only [drift_inverse, kick_inverse]

theorem comparisonVerlet_measurePreserving (g : E → E) (hg : Measurable g) (h vstar : ℝ) :
    MeasurePreserving (comparisonVerlet g h vstar) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := by
  have he : comparisonVerlet g h vstar = fun z =>
      kick g (h/2) (drift (h/2) (speedFlip vstar (drift (h/2) (kick g (h/2) z)))) :=
    funext (comparisonVerlet_factorization g h vstar)
  rw [he]
  exact (kick_measurePreserving g hg (h/2)).comp
    ((drift_measurePreserving (h/2)).comp
      ((speedFlip_measurePreserving vstar).comp
        ((drift_measurePreserving (h/2)).comp (kick_measurePreserving g hg (h/2)))))

/-- A literal Borel equivalence; its inverse uses the negative step size. -/
def comparisonVerletEquiv (g : E → E) (hg : Measurable g) (h vstar : ℝ) :
    (E×E) ≃ᵐ (E×E) where
  toFun := comparisonVerlet g h vstar
  invFun := comparisonVerlet g (-h) vstar
  left_inv := comparisonVerlet_inverse g h vstar
  right_inv := by intro z; simpa only [neg_neg] using comparisonVerlet_inverse g (-h) vstar z
  measurable_toFun := (comparisonVerlet_measurePreserving g hg h vstar).measurable
  measurable_invFun := (comparisonVerlet_measurePreserving g hg (-h) vstar).measurable

theorem comparisonVerlet_energy_identity (U : E → ℝ) (g : E → E) (h vstar : ℝ) (z : E×E) :
    phaseEnergy U (comparisonVerlet g h vstar z)-phaseEnergy U z =
      gradientCorrection g h (comparisonVerlet g h vstar z).1-gradientCorrection g h z.1+
        comparisonDefect U g h vstar z := by
  by_cases hz : ‖flightVelocity g h z‖ ≤ vstar
  · simp only [comparisonVerlet, comparisonDefect, hz, ite_true]
    exact verlet_energy_identity U g h z
  · simp only [comparisonVerlet, comparisonDefect, hz, ite_false, phaseEnergy_velocityFlip]
    simp [velocityFlip]

theorem comparisonDefect_bound {U : E → ℝ} {L LH h vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hh : 0 ≤ h) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h) (z : E×E) :
    comparisonDefect U (gradient U) h vstar z ≤
      (0.02:ℝ)*h*‖flightVelocity (gradient U) h z‖^2 := by
  by_cases hz : ‖flightVelocity (gradient U) h z‖ ≤ vstar
  · simp only [comparisonDefect, hz, ite_true]
    have ht := verlet_trapezoidDefect_lipschitz_bound U (gradient U) (hessian U)
      a.hasGradientAt a.hasHessianAt a.continuous_hessian LH h hh a2.lipschitz z
    have hp := mul_le_mul_of_nonneg_left hz
      (show 0 ≤ LH*h^3/12*‖flightVelocity (gradient U) h z‖^2 by positivity)
    have hs := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖flightVelocity (gradient U) h z‖)
    have hab := le_abs_self (trapezoidDefect U (gradient U) z.1 (verlet (gradient U) h z).1)
    nlinarith
  · simp only [comparisonDefect, hz, ite_false]
    positivity

theorem comparisonVerlet_modifiedEnergy_growth {U : E → ℝ} {L LH h vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h) (z : E×E) :
    modifiedEnergy U h (comparisonVerlet (gradient U) h vstar z) ≤
      (1+(0.081:ℝ)*h)*modifiedEnergy U h z := by
  have hid := comparisonVerlet_energy_identity U (gradient U) h vstar z
  have ht := comparisonDefect_bound a a2 hh hLH hscale z
  have hf := a.normalized_flight_energy_bound hstar hzero hL z
  have hg := (lyapunov_energy_bounds a hstar hzero hL z).2.2.1
  have hH := a.normalized_energy_nonnegative hstar hzero z
  have hG : 0 ≤ modifiedEnergy U h z := by nlinarith
  have hfh := mul_le_mul_of_nonneg_left hf hh
  have hgh := mul_le_mul_of_nonneg_left hg hh
  have hn := mul_nonneg hh hG
  unfold modifiedEnergy
  unfold modifiedEnergy at hgh hn
  nlinarith

/-- All assertions of Lemma 5.7, including the actual Borel inverse and volume law. -/
theorem lemma_5_7 {U : E → ℝ} {L LH h vstar : ℝ}
    (a : A1 U 1 L) (a2 : A2 U LH) (hstar : a.minimizer=0) (hzero : U 0=0)
    (hh : 0 ≤ h) (hL : h^2*L ≤ 1/64) (hLH : 0 ≤ LH)
    (hscale : LH*h^3/12*vstar ≤ (0.02:ℝ)*h) :
    MeasurePreserving (comparisonVerlet (gradient U) h vstar)
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) ∧
    Function.Bijective (comparisonVerlet (gradient U) h vstar) ∧
    Measurable (comparisonVerlet (gradient U) (-h) vstar) ∧
    ∀ z : E×E,
      phaseEnergy U (comparisonVerlet (gradient U) h vstar z)-phaseEnergy U z =
        gradientCorrection (gradient U) h (comparisonVerlet (gradient U) h vstar z).1-
          gradientCorrection (gradient U) h z.1+comparisonDefect U (gradient U) h vstar z ∧
      comparisonDefect U (gradient U) h vstar z ≤
        (0.02:ℝ)*h*‖flightVelocity (gradient U) h z‖^2 ∧
      modifiedEnergy U h (comparisonVerlet (gradient U) h vstar z) ≤
        (1+(0.081:ℝ)*h)*modifiedEnergy U h z := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  refine ⟨comparisonVerlet_measurePreserving _ hg h vstar,
    (comparisonVerletEquiv _ hg h vstar).bijective,
    (comparisonVerlet_measurePreserving _ hg (-h) vstar).measurable, ?_⟩
  intro z
  exact ⟨comparisonVerlet_energy_identity U (gradient U) h vstar z,
    comparisonDefect_bound a a2 hh hLH hscale z,
    comparisonVerlet_modifiedEnergy_growth a a2 hstar hzero hh hL hLH hscale z⟩

end
end PersistencePays
#print axioms PersistencePays.comparisonVerletEquiv
#print axioms PersistencePays.comparisonVerlet_measurePreserving
#print axioms PersistencePays.comparisonVerlet_modifiedEnergy_growth

#print axioms PersistencePays.lemma_5_7
