import PersistencePays.CouplingTV
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-! Jointly measurable common and residual parts of two probability kernels. -/
noncomputable section
namespace PersistencePays.MaximalCoupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [MeasurableSpace.CountablyGenerated S]

/-- The density of the first kernel in the sum, clipped only on a null set. -/
def mixtureDensity (K J : Kernel A S) (a : A) (x : S) : ℝ :=
  min 1 (Kernel.rnDerivAux K (K+J) a x)

@[fun_prop] theorem mixtureDensity_measurable (K J : Kernel A S) :
    Measurable (fun p : A×S => mixtureDensity K J p.1 p.2) := by
  unfold mixtureDensity
  fun_prop

theorem mixtureDensity_nonnegative (K J : Kernel A S) (a : A) (x : S) :
    0 ≤ mixtureDensity K J a x := by
  exact le_min zero_le_one (Kernel.rnDerivAux_nonneg (le_add_of_nonneg_right bot_le))

theorem mixtureDensity_le_one (K J : Kernel A S) (a : A) (x : S) :
    mixtureDensity K J a x ≤ 1 := min_le_left _ _

theorem mixtureDensity_ae (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    mixtureDensity K J a =ᵐ[(K+J) a] Kernel.rnDerivAux K (K+J) a := by
  filter_upwards [Kernel.rnDerivAux_le_one (κ:=K) (η:=K+J)
    (le_add_of_nonneg_right bot_le) (a:=a)] with x hx
  exact min_eq_right hx

theorem density_first (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    (K+J).withDensity (fun a x => ENNReal.ofReal (mixtureDensity K J a x)) = K := by
  refine Eq.trans ?_ (Kernel.withDensity_rnDerivAux K J)
  apply Kernel.withDensity_congr_ae
  · fun_prop
  · fun_prop
  · intro a
    filter_upwards [mixtureDensity_ae K J a] with x hx
    simp [hx, ENNReal.ofNNReal_toNNReal]

theorem density_second (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    (K+J).withDensity (fun a x => ENNReal.ofReal (1-mixtureDensity K J a x)) = J := by
  refine Eq.trans ?_ (Kernel.withDensity_one_sub_rnDerivAux K J)
  apply Kernel.withDensity_congr_ae
  · fun_prop
  · fun_prop
  · intro a
    filter_upwards [mixtureDensity_ae K J a] with x hx
    simp [hx, ENNReal.ofNNReal_toNNReal]

def overlapDensity (K J : Kernel A S) (a : A) (x : S) : ℝ :=
  min (mixtureDensity K J a x) (1-mixtureDensity K J a x)

def leftDensity (K J : Kernel A S) (a : A) (x : S) : ℝ :=
  mixtureDensity K J a x - overlapDensity K J a x

def rightDensity (K J : Kernel A S) (a : A) (x : S) : ℝ :=
  1-mixtureDensity K J a x - overlapDensity K J a x

@[fun_prop] theorem overlapDensity_measurable (K J : Kernel A S) :
    Measurable (fun p : A×S => overlapDensity K J p.1 p.2) := by
  unfold overlapDensity; fun_prop
@[fun_prop] theorem leftDensity_measurable (K J : Kernel A S) :
    Measurable (fun p : A×S => leftDensity K J p.1 p.2) := by
  unfold leftDensity; fun_prop
@[fun_prop] theorem rightDensity_measurable (K J : Kernel A S) :
    Measurable (fun p : A×S => rightDensity K J p.1 p.2) := by
  unfold rightDensity; fun_prop

theorem overlapDensity_bounds (K J : Kernel A S) (a : A) (x : S) :
    0 ≤ overlapDensity K J a x ∧ overlapDensity K J a x ≤ 1 := by
  have hp := mixtureDensity_nonnegative K J a x
  have hq := mixtureDensity_le_one K J a x
  exact ⟨le_min hp (by linarith), (min_le_left _ _).trans hq⟩

theorem leftDensity_bounds (K J : Kernel A S) (a : A) (x : S) :
    0 ≤ leftDensity K J a x ∧ leftDensity K J a x ≤ 1 := by
  have hp := mixtureDensity_le_one K J a x
  have hc := (overlapDensity_bounds K J a x).1
  have hcp : overlapDensity K J a x ≤ mixtureDensity K J a x := min_le_left _ _
  unfold leftDensity
  constructor <;> linarith

theorem rightDensity_bounds (K J : Kernel A S) (a : A) (x : S) :
    0 ≤ rightDensity K J a x ∧ rightDensity K J a x ≤ 1 := by
  have hp := mixtureDensity_nonnegative K J a x
  have hc := (overlapDensity_bounds K J a x).1
  have hcq : overlapDensity K J a x ≤ 1-mixtureDensity K J a x := min_le_right _ _
  unfold rightDensity
  constructor <;> linarith

def overlapKernel (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] : Kernel A S :=
  (K+J).withDensity (fun a x => ENNReal.ofReal (overlapDensity K J a x))
def leftKernel (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] : Kernel A S :=
  (K+J).withDensity (fun a x => ENNReal.ofReal (leftDensity K J a x))
def rightKernel (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] : Kernel A S :=
  (K+J).withDensity (fun a x => ENNReal.ofReal (rightDensity K J a x))

instance overlapKernel_finite (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    IsFiniteKernel (overlapKernel K J) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded (K+J) (B:=1) (by simp)
  intro a x
  exact ENNReal.ofReal_le_one.mpr (overlapDensity_bounds K J a x).2
instance leftKernel_finite (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    IsFiniteKernel (leftKernel K J) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded (K+J) (B:=1) (by simp)
  intro a x
  exact ENNReal.ofReal_le_one.mpr (leftDensity_bounds K J a x).2
instance rightKernel_finite (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    IsFiniteKernel (rightKernel K J) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded (K+J) (B:=1) (by simp)
  intro a x
  exact ENNReal.ofReal_le_one.mpr (rightDensity_bounds K J a x).2

theorem overlap_add_left (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    overlapKernel K J + leftKernel K J = K := by
  rw [overlapKernel, leftKernel, ← Kernel.withDensity_add_right (by fun_prop) (by fun_prop)]
  refine Eq.trans ?_ (density_first K J)
  apply Kernel.withDensity_congr_ae (K+J)
    (by simp only [Function.uncurry_def, Pi.add_apply]; fun_prop) (by fun_prop)
  intro a
  apply Filter.Eventually.of_forall
  intro x
  change ENNReal.ofReal (overlapDensity K J a x)+ENNReal.ofReal (leftDensity K J a x) = _
  rw [← ENNReal.ofReal_add (overlapDensity_bounds K J a x).1 (leftDensity_bounds K J a x).1]
  congr 1
  unfold leftDensity
  ring

theorem overlap_add_right (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] :
    overlapKernel K J + rightKernel K J = J := by
  rw [overlapKernel, rightKernel, ← Kernel.withDensity_add_right (by fun_prop) (by fun_prop)]
  refine Eq.trans ?_ (density_second K J)
  apply Kernel.withDensity_congr_ae (K+J)
    (by simp only [Function.uncurry_def, Pi.add_apply]; fun_prop) (by fun_prop)
  intro a
  apply Filter.Eventually.of_forall
  intro x
  change ENNReal.ofReal (overlapDensity K J a x)+ENNReal.ofReal (rightDensity K J a x) = _
  rw [← ENNReal.ofReal_add (overlapDensity_bounds K J a x).1 (rightDensity_bounds K J a x).1]
  congr 1
  unfold rightDensity
  ring

def positiveResidualSet (K J : Kernel A S) (a : A) : Set S :=
  {x | 1/2 < mixtureDensity K J a x}

theorem positiveResidualSet_measurable (K J : Kernel A S) (a : A) :
    MeasurableSet (positiveResidualSet K J a) := by
  unfold positiveResidualSet
  exact measurableSet_lt measurable_const ((mixtureDensity_measurable K J).comp
    (f:=fun x : S => (a,x)) measurable_prodMk_left)

theorem leftKernel_supported (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    leftKernel K J a (positiveResidualSet K J a)ᶜ = 0 := by
  rw [leftKernel, Kernel.withDensity_apply' _ (by fun_prop)]
  apply setLIntegral_eq_zero_iff (positiveResidualSet_measurable K J a).compl (by fun_prop) |>.mpr
  apply Filter.Eventually.of_forall
  intro x hx
  have hp : mixtureDensity K J a x ≤ 1/2 := le_of_not_gt hx
  have hc : overlapDensity K J a x = mixtureDensity K J a x := min_eq_left (by linarith)
  simp [leftDensity, hc]

theorem rightKernel_supported (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    rightKernel K J a (positiveResidualSet K J a) = 0 := by
  rw [rightKernel, Kernel.withDensity_apply' _ (by fun_prop)]
  apply setLIntegral_eq_zero_iff (positiveResidualSet_measurable K J a) (by fun_prop) |>.mpr
  apply Filter.Eventually.of_forall
  intro x hx
  have hp : 1/2 < mixtureDensity K J a x := hx
  have hc : overlapDensity K J a x = 1-mixtureDensity K J a x := min_eq_right (by linarith)
  simp [rightDensity, hc]


/-- The common mass is coupled identically; the two residuals are sampled
independently after normalization by their common mass. -/
def maximalKernel (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] : Kernel A (S×S) :=
  (overlapKernel K J).map (fun x => (x,x)) +
    (leftKernel K J ×ₖ rightKernel K J).withDensity
      (fun a _ => (leftKernel K J a univ)⁻¹)

theorem maximalKernel_apply (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    maximalKernel K J a =
      (overlapKernel K J a).map (fun x => (x,x)) +
        (leftKernel K J a univ)⁻¹ • (leftKernel K J a).prod (rightKernel K J a) := by
  rw [maximalKernel, Kernel.add_apply, Kernel.map_apply _ (by fun_prop),
    Kernel.withDensity_apply _ (by
      exact ((Kernel.measurable_coe (leftKernel K J) MeasurableSet.univ).comp measurable_fst).inv),
    Kernel.prod_apply, withDensity_const]


end PersistencePays.MaximalCoupling
#print axioms PersistencePays.MaximalCoupling.overlap_add_left
#print axioms PersistencePays.MaximalCoupling.overlap_add_right
