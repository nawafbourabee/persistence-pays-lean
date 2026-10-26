import PersistencePays.GaussianTilt
import PersistencePays.GaussianOptimization

/-! The exact soft-coordinate crossing constant of Appendix B. -/

noncomputable section
namespace PersistencePays.GaussianLowerBound

open MeasureTheory ProbabilityTheory Set

theorem tilt_denominator_bound (w : ℝ) :
    1 + w ^ 2 / 4 ≤ tiltD w * (tiltC w + tiltA w) := by
  by_cases hw : w ^ 2 ≤ 2
  · have hca : 1 + w ^ 2 / 4 ≤ tiltC w + tiltA w := by
      have hp : 0 ≤ (2 - w ^ 2) * (4 - w ^ 2) := mul_nonneg (by linarith) (by linarith)
      dsimp [tiltC, tiltA]
      nlinarith
    have hd : 1 ≤ tiltD w := by
      dsimp [tiltD]
      have h6 : 0 ≤ w ^ 6 := by positivity
      linarith
    have hp := mul_le_mul_of_nonneg_right hd (tiltC_add_A_pos w).le
    linarith
  · have hw' : 2 ≤ w ^ 2 := le_of_lt (lt_of_not_ge hw)
    have hd : 1 + w ^ 4 / 32 ≤ tiltD w := by
      have hp := mul_nonneg (sq_nonneg (w ^ 2)) (sub_nonneg.mpr hw')
      dsimp [tiltD]
      nlinarith
    have hca : (3 / 2 : ℝ) ≤ tiltC w + tiltA w := by
      dsimp [tiltC, tiltA]
      nlinarith [sq_nonneg (w ^ 2 - 2)]
    have hp := mul_le_mul hd hca (by norm_num : (0 : ℝ) ≤ 3 / 2) (tiltD_pos w).le
    have hl : 1 + w ^ 2 / 4 ≤ (1 + w ^ 4 / 32) * (3 / 2 : ℝ) := by
      nlinarith [sq_nonneg (w ^ 2 - 3), sq_nonneg w]
    exact hl.trans hp

theorem rho_tilt_ratio_bound (w : ℝ) (hw : 0 < w) :
    gaussianRho w * (tiltBeta w / tiltAlpha w) ≤ w / Real.sqrt 2 := by
  have hD := tiltD_pos w
  have hCA := tiltC_add_A_pos w
  have hα := tiltAlpha_pos w
  have hρ : (gaussianRho w) ^ 2 = 1 / tiltD w := by
    rw [gaussianRho, inv_pow, Real.sq_sqrt (show 0 ≤ 1 + w ^ 6 / 64 by positivity)]
    simp [tiltD, one_div]
  have hratio : (gaussianRho w * (tiltBeta w / tiltAlpha w)) ^ 2 =
      (tiltC w - tiltA w) / (tiltD w * (tiltC w + tiltA w)) := by
    rw [mul_pow, div_pow, hρ, tiltBeta_sq hw, tiltAlpha_sq]
    field_simp
  apply (sq_le_sq₀ (mul_nonneg (gaussianRho_pos w).le
      (div_nonneg (tiltBeta_pos hw).le hα.le))
    (by positivity : 0 ≤ w / Real.sqrt 2)).mp
  rw [hratio, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (mul_pos hD hCA)).mpr
  have hh := mul_le_mul_of_nonneg_left (tilt_denominator_bound w) (sq_nonneg w)
  have he : 2 * (tiltC w - tiltA w) = w ^ 2 * (1 + w ^ 2 / 4) := by
    dsimp [tiltC, tiltA]
    ring
  nlinarith

def scalarCrossing (w : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ 0 ∧ 0 < scalarVerletPosition w z}

theorem scalarCrossing_measurable (w : ℝ) : MeasurableSet (scalarCrossing w) := by
  unfold scalarCrossing
  have hm : Measurable (scalarVerletPosition w) := by unfold scalarVerletPosition; fun_prop
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const hm)

theorem tilt_crossing_preimage (w : ℝ) (hw : 0 < w) :
    tiltMap w ⁻¹' scalarCrossing w =
      {p : ℝ × ℝ | p.1 ≤ (tiltBeta w / tiltAlpha w) * p.2 ∧
        -(tiltBeta w / tiltAlpha w) * p.2 < p.1} := by
  ext p
  change ((tiltMap w p).1 ≤ 0 ∧ 0 < scalarVerletPosition w (tiltMap w p)) ↔ _
  rw [tiltMap_position hw]
  change (tiltAlpha w * p.1 + -tiltBeta w * p.2 ≤ 0 ∧
    0 < tiltAlpha w * p.1 + tiltBeta w * p.2) ↔ _
  have hα := tiltAlpha_pos w
  have hp : tiltAlpha w * ((tiltBeta w / tiltAlpha w) * p.2) = tiltBeta w * p.2 := by
    field_simp
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith
  · intro ⟨h1, h2⟩
    have ha := mul_le_mul_of_nonneg_left h1 hα.le
    have hb := mul_lt_mul_of_pos_left h2 hα
    constructor <;> linarith

/-- The actual weighted crossing measure satisfies the paper's constant,
without assuming a Gaussian quadrant formula. -/
theorem weighted_soft_crossing_bound (w : ℝ) (hw : 0 < w) :
    2 * (scalarGaussianPair.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-scalarVerletWork w z / 2)))).real
        (scalarCrossing w) ≤ w / Real.sqrt 2 := by
  rw [scalarGaussian_verlet_tilt_law w hw, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity), map_measureReal_apply (by fun_prop)
      (scalarCrossing_measurable w), tilt_crossing_preimage w hw]
  have hb := standard_normal_wedge_bound (tiltBeta w / tiltAlpha w)
    (div_nonneg (tiltBeta_pos hw).le (tiltAlpha_pos w).le)
  have hρ : 0 ≤ 1 / Real.sqrt (tiltD w) := by positivity
  have hm := mul_le_mul_of_nonneg_left hb hρ
  have hc := rho_tilt_ratio_bound w hw
  simp only [gaussianRho, ← one_div] at hc
  change (1 / Real.sqrt (tiltD w)) * (tiltBeta w / tiltAlpha w) ≤ _ at hc
  change 2 * ((1 / Real.sqrt (tiltD w)) *
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real _) ≤ _
  linarith

end PersistencePays.GaussianLowerBound

#print axioms PersistencePays.GaussianLowerBound.weighted_soft_crossing_bound
