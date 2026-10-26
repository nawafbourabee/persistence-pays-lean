import PersistencePays.GaussianLowerBound
import PersistencePays.ScheduledCachedSampler

/-! Proposition 2.4 with the literal finite-array cached implementation and all queries counted. -/
noncomputable section
namespace PersistencePays.GaussianLowerBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def gaussianWarmStart (k : ℕ) (m L : ℝ) :=
  (2 : ℝ≥0∞) • (extendedTarget (twoScalePotential k m L)).restrict
    (positionCylinder (softHalfspace k))

def gaussianImplementedLaw (k : ℕ) (m L h r σ : ℝ) (refresh : ℕ → Bool) (n : ℕ) :=
  ((gaussianWarmStart k m L).prod
    (Measure.pi (fun _ : Fin n => CachedOBABO.scheduledNoise
      (E:=EuclideanSpace ℝ (Fin (k+1)))))).map
    (fun p => CachedOBABO.projection (CachedOBABO.simulateSchedule (twoScalePotential k m L)
      (gradient (twoScalePotential k m L)) h r σ refresh n p.1 p.2))

theorem gaussianImplementedLaw_eq (k : ℕ) (m L h r σ : ℝ) (refresh : ℕ → Bool) (n : ℕ) :
    gaussianImplementedLaw k m L h r σ refresh n = gaussianAttemptLaw k m L h r σ refresh n := by
  let : SFinite (gaussianWarmStart k m L) := by
    unfold gaussianWarmStart extendedTarget phaseGibbs positionGibbs
    infer_instance
  exact CachedOBABO.simulateSchedule_law (twoScalePotential k m L)
    (twoScalePotential_measurable k m L) (gradient (twoScalePotential k m L))
    (twoScaleGradient_measurable k m L) h r σ refresh (gaussianWarmStart k m L) n

/-- Every realization of the implemented sampler pays this many gradient queries
if its position marginal has reached TV accuracy one quarter. -/
theorem proposition_2_4_gradient_cost (k : ℕ) (hk : 1 ≤ k) (m L h r σ : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hnorm : r^2+σ^2=1)
    (refresh : ℕ → Bool) (n : ℕ)
    (haccurate : probabilityTV
      ((gaussianImplementedLaw k m L h r σ refresh n).map (fun z => z.1.1))
        (positionGibbs (twoScalePotential k m L)) ≤ 1/4)
    (z : ((EuclideanSpace ℝ (Fin (k+1))) × (EuclideanSpace ℝ (Fin (k+1)))) × ℝ)
    (b : Fin n → ((EuclideanSpace ℝ (Fin (k+1))) × (EuclideanSpace ℝ (Fin (k+1)))) × ℝ) :
    Real.sqrt 2/8 * Real.sqrt (L/m) * ((k+1:ℕ):ℝ)^(1/6:ℝ) + 1 ≤
      (CachedOBABO.simulateSchedule (twoScalePotential k m L)
        (gradient (twoScalePotential k m L)) h r σ refresh n z b).calls := by
  rw [gaussianImplementedLaw_eq] at haccurate
  have hn : Real.sqrt 2/8 * Real.sqrt (L/m) * ((k+1:ℕ):ℝ)^(1/6:ℝ) ≤ (n:ℝ) := by
    by_contra hn
    exact (not_lt_of_ge haccurate) (proposition_2_4 k hk m L h r σ hm hmL hh hnorm refresh n
      (lt_of_not_ge hn))
  rw [CachedOBABO.simulateSchedule_queries]
  push_cast
  norm_num only [Nat.cast_add, Nat.cast_one] at hn
  linarith

end PersistencePays.GaussianLowerBound
#print axioms PersistencePays.GaussianLowerBound.proposition_2_4_gradient_cost
