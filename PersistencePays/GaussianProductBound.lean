import PersistencePays.GaussianSoftCrossing
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact finite-product acceptance/crossing factorization for Appendix B. -/
noncomputable section
namespace PersistencePays.GaussianLowerBound
open MeasureTheory ProbabilityTheory Set

/-- The Gaussian half-power bound for the Metropolis acceptance function. -/
theorem metropolis_le_half_exp (y : ℝ) : min 1 (Real.exp (-y)) ≤ Real.exp (-y / 2) := by
  by_cases hy : 0 ≤ y
  · exact (min_le_right _ _).trans (Real.exp_le_exp.mpr (by linarith))
  · exact (min_le_left _ _).trans (Real.one_le_exp (by linarith))

def softFactor (w : ℝ) : (ℝ × ℝ) → ℝ :=
  (scalarCrossing w).indicator (fun z => Real.exp (-scalarVerletWork w z / 2))

def coordinateFactor (n : ℕ) (s t : ℝ) : Fin (n+1) → (ℝ × ℝ) → ℝ :=
  Fin.cases (softFactor s) (fun _ z => Real.exp (-scalarVerletWork t z / 2))

def coordinateFrequency (n : ℕ) (s t : ℝ) : Fin (n+1) → ℝ :=
  Fin.cases s (fun _ => t)

def coordinateWork (n : ℕ) (s t : ℝ) (z : Fin (n+1) → ℝ × ℝ) : ℝ :=
  ∑ i, scalarVerletWork (coordinateFrequency n s t i) (z i)

def coordinateCrossing (n : ℕ) (s : ℝ) : Set (Fin (n+1) → ℝ × ℝ) :=
  {z | z 0 ∈ scalarCrossing s}

def productGaussianPair (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun _ => scalarGaussianPair)

instance productGaussianPair_probability (n : ℕ) : IsProbabilityMeasure (productGaussianPair n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => scalarGaussianPair)))

theorem softFactor_nonnegative (w : ℝ) (z : ℝ × ℝ) : 0 ≤ softFactor w z := by
  unfold softFactor
  exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem softFactor_integrable (w : ℝ) (hw : 0 < w) : Integrable (softFactor w) scalarGaussianPair :=
  (integrable_scalarGaussian_verlet_tilt w hw).indicator (scalarCrossing_measurable w)

theorem softFactor_integral (w : ℝ) (hw : 0 < w) :
    (∫ z, softFactor w z ∂scalarGaussianPair) =
      (scalarGaussianPair.withDensity
        (fun z => ENNReal.ofReal (Real.exp (-scalarVerletWork w z / 2)))).real
          (scalarCrossing w) := by
  rw [Measure.real, withDensity_apply _ (scalarCrossing_measurable w)]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (softFactor_nonnegative w)) (softFactor_integrable w hw).aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator (scalarCrossing_measurable w)]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ scalarCrossing w <;> simp [softFactor, hz]

theorem softFactor_integral_bound (w : ℝ) (hw : 0 < w) :
    (∫ z, softFactor w z ∂scalarGaussianPair) ≤ w / (2 * Real.sqrt 2) := by
  rw [softFactor_integral w hw]
  have hb := weighted_soft_crossing_bound w hw
  have hs : 0 < Real.sqrt (2:ℝ) := by positivity
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (2:ℝ))).mpr
  have hh := (le_div_iff₀ hs).mp hb
  nlinarith

theorem coordinateFactor_nonnegative (n : ℕ) (s t : ℝ) (i : Fin (n+1)) (z : ℝ×ℝ) :
    0 ≤ coordinateFactor n s t i z := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact softFactor_nonnegative s z
  · exact (Real.exp_pos _).le

theorem coordinateFactor_integrable (n : ℕ) (s t : ℝ) (hs : 0<s) (ht : 0<t)
    (i : Fin (n+1)) : Integrable (coordinateFactor n s t i) scalarGaussianPair := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact softFactor_integrable s hs
  · exact integrable_scalarGaussian_verlet_tilt t ht

theorem coordinate_product_integrable (n : ℕ) (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    Integrable (fun z => ∏ i, coordinateFactor n s t i (z i)) (productGaussianPair (n+1)) :=
  Integrable.fintype_prod (coordinateFactor_integrable n s t hs ht)

theorem coordinate_product_integral (n : ℕ) (s t : ℝ) (ht : 0<t) :
    (∫ z, ∏ i, coordinateFactor n s t i (z i) ∂productGaussianPair (n+1)) =
      (∫ z, softFactor s z ∂scalarGaussianPair) * gaussianRho t ^ n := by
  rw [productGaussianPair, integral_fintype_prod_eq_prod, Fin.prod_univ_succ]
  simp only [coordinateFactor, Fin.cases_zero, Fin.cases_succ,
    scalarGaussian_verlet_tilt_expectation t ht, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp [gaussianRho, tiltD, one_div]

theorem coordinate_product_identity (n : ℕ) (s t : ℝ) (z : Fin (n+1) → ℝ×ℝ) :
    (∏ i, coordinateFactor n s t i (z i)) =
      (coordinateCrossing n s).indicator (fun z => Real.exp (-coordinateWork n s t z / 2)) z := by
  rw [Fin.prod_univ_succ]
  simp only [coordinateFactor, Fin.cases_zero, Fin.cases_succ]
  by_cases hz : z 0 ∈ scalarCrossing s
  · simp only [softFactor, indicator_of_mem hz]
    rw [← Real.exp_sum, ← Real.exp_add]
    rw [indicator_of_mem (show z ∈ coordinateCrossing n s from hz)]
    congr 1
    simp only [coordinateWork, Fin.sum_univ_succ, coordinateFrequency,
      Fin.cases_zero, Fin.cases_succ]
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
    ring
  · simp only [softFactor, indicator_of_notMem hz, zero_mul]
    rw [indicator_of_notMem (show z ∉ coordinateCrossing n s from hz)]

theorem product_accepted_crossing_bound (n : ℕ) (s t : ℝ) (hs : 0<s) (ht : 0<t) :
    (∫⁻ z, (coordinateCrossing n s).indicator
      (fun z => ENNReal.ofReal (min 1 (Real.exp (-coordinateWork n s t z)))) z
        ∂productGaussianPair (n+1)) ≤
      ENNReal.ofReal (s / (2 * Real.sqrt 2) * gaussianRho t ^ n) := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (∏ i, coordinateFactor n s t i (z i))
        ∂productGaussianPair (n+1) := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [coordinate_product_identity]
      by_cases hz : z ∈ coordinateCrossing n s
      · simp only [indicator_of_mem hz]
        exact ENNReal.ofReal_le_ofReal (metropolis_le_half_exp _)
      · simp [indicator_of_notMem hz]
    _ = ENNReal.ofReal ((∫ z, softFactor s z ∂scalarGaussianPair) * gaussianRho t ^ n) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (coordinate_product_integrable n s t hs ht)
        (Filter.Eventually.of_forall (fun z => Finset.prod_nonneg
          (fun i _ => coordinateFactor_nonnegative n s t i (z i)))),
        coordinate_product_integral n s t ht]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (softFactor_integral_bound s hs) (pow_nonneg (gaussianRho_pos t).le _))

end PersistencePays.GaussianLowerBound
#print axioms PersistencePays.GaussianLowerBound.product_accepted_crossing_bound
