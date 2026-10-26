import PersistencePays.GaussianBridgeLaw
import Mathlib.LinearAlgebra.Basis.Fin

/-! The actual two-dimensional Gaussian tilt in Appendix B. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal

/-- A two-by-two real matrix acting on ordinary pairs. -/
def pairLinear (a b c d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun z := (a*z.1+b*z.2, c*z.1+d*z.2)
  map_add' := by intro x y; ext <;> dsimp <;> ring
  map_smul' := by intro t x; ext <;> dsimp <;> ring

theorem pairLinear_det (a b c d : ℝ) :
    LinearMap.det (pairLinear a b c d) = a*d-b*c := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Basis.finTwoProd, LinearEquiv.finTwoArrow, pairLinear]

def pairLinearEquiv (a b c d : ℝ) (h : a*d-b*c ≠ 0) :
    (ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ where
  toLinearMap := pairLinear a b c d
  invFun z := ((d*z.1-b*z.2)/(a*d-b*c), (-c*z.1+a*z.2)/(a*d-b*c))
  left_inv := by
    intro z
    ext <;> dsimp [pairLinear] <;> ring_nf at h ⊢ <;> field_simp [h] <;> ring
  right_inv := by
    intro z
    ext <;> dsimp [pairLinear] <;> ring_nf at h ⊢ <;> field_simp [h] <;> ring

def pairMeasurableEquiv (a b c d : ℝ) (h : a*d-b*c ≠ 0) :
    (ℝ × ℝ) ≃ᵐ ℝ × ℝ :=
  (pairLinearEquiv a b c d h).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem pairLinear_map_volume (a b c d : ℝ) (h : a*d-b*c ≠ 0) :
    Measure.map (pairLinear a b c d) ((volume : Measure ℝ).prod volume) =
      ENNReal.ofReal |(a*d-b*c)⁻¹| • ((volume : Measure ℝ).prod volume) := by
  have hd : LinearMap.det (pairLinear a b c d) ≠ 0 := by rwa [pairLinear_det]
  simpa only [pairLinear_det] using
    (Measure.map_linearMap_addHaar_eq_smul_addHaar
      ((volume : Measure ℝ).prod volume) hd)

def tiltA (w : ℝ) := 1-w^2/2
def tiltC (w : ℝ) := 1+w^4/8
def tiltD (w : ℝ) := 1+w^6/64
def tiltAlpha (w : ℝ) := Real.sqrt ((tiltC w+tiltA w)/(2*tiltD w))
def tiltBeta (w : ℝ) := Real.sqrt ((tiltC w-tiltA w)/(2*tiltD w))
def scalarVerletPosition (w : ℝ) (z : ℝ × ℝ) := tiltA w*z.1+w*z.2
def scalarVerletWork (w : ℝ) (z : ℝ × ℝ) :=
  w^2/8*((scalarVerletPosition w z)^2-z.1^2)
def tiltMap (w : ℝ) := pairLinear (tiltAlpha w) (-tiltBeta w)
  ((1-tiltA w)*tiltAlpha w/w) ((1+tiltA w)*tiltBeta w/w)

theorem tiltD_pos (w : ℝ) : 0 < tiltD w := by
  dsimp [tiltD]
  positivity

theorem tiltC_add_A_pos (w : ℝ) : 0 < tiltC w+tiltA w := by
  dsimp [tiltC, tiltA]
  nlinarith [sq_nonneg (w^2-2)]

theorem tiltC_sub_A_pos {w : ℝ} (hw : 0 < w) : 0 < tiltC w-tiltA w := by
  dsimp [tiltC, tiltA]
  nlinarith [sq_pos_of_pos hw, sq_nonneg (w^2)]

theorem tilt_covariance_identity (w : ℝ) :
    (tiltC w)^2-(tiltA w)^2 = w^2*tiltD w := by
  dsimp [tiltC, tiltA, tiltD]
  ring

theorem tiltAlpha_pos (w : ℝ) : 0 < tiltAlpha w :=
  Real.sqrt_pos.2 (div_pos (tiltC_add_A_pos w) (mul_pos (by norm_num) (tiltD_pos w)))

theorem tiltBeta_pos {w : ℝ} (hw : 0 < w) : 0 < tiltBeta w :=
  Real.sqrt_pos.2 (div_pos (tiltC_sub_A_pos hw) (mul_pos (by norm_num) (tiltD_pos w)))

theorem tiltAlpha_sq (w : ℝ) :
    (tiltAlpha w)^2=(tiltC w+tiltA w)/(2*tiltD w) :=
  Real.sq_sqrt (le_of_lt (div_pos (tiltC_add_A_pos w)
    (mul_pos (by norm_num) (tiltD_pos w))))

theorem tiltBeta_sq {w : ℝ} (hw : 0 < w) :
    (tiltBeta w)^2=(tiltC w-tiltA w)/(2*tiltD w) :=
  Real.sq_sqrt (le_of_lt (div_pos (tiltC_sub_A_pos hw)
    (mul_pos (by norm_num) (tiltD_pos w))))


theorem tiltMap_position {w : ℝ} (hw : 0 < w) (z : ℝ × ℝ) :
    scalarVerletPosition w (tiltMap w z) = tiltAlpha w*z.1+tiltBeta w*z.2 := by
  dsimp [scalarVerletPosition, tiltMap, pairLinear]
  field_simp [hw.ne']
  ring

theorem tiltMap_quadratic {w : ℝ} (hw : 0 < w) (z : ℝ × ℝ) :
    (tiltMap w z).1^2+(tiltMap w z).2^2+scalarVerletWork w (tiltMap w z) =
      z.1^2+z.2^2 := by
  have hα : (tiltAlpha w)^2*(1+w^2/4)=1 := by
    rw [tiltAlpha_sq]
    dsimp [tiltC, tiltA, tiltD]
    field_simp
    ring
  have hβ : (tiltBeta w)^2*(4-w^2+w^4/4)=w^2 := by
    rw [tiltBeta_sq hw]
    dsimp [tiltC, tiltA, tiltD]
    field_simp
    ring
  calc
    _ = (tiltAlpha w)^2*(1+w^2/4)*z.1^2 +
        ((tiltBeta w)^2*(4-w^2+w^4/4)/w^2)*z.2^2 := by
      rw [scalarVerletWork, tiltMap_position hw]
      simp only [tiltMap, pairLinear, LinearMap.coe_mk, AddHom.coe_mk, tiltA]
      field_simp
      ring
    _ = _ := by rw [hα, hβ, div_self (pow_ne_zero _ hw.ne')]; ring

theorem tiltAlpha_mul_Beta {w : ℝ} (hw : 0 < w) :
    2*tiltAlpha w*tiltBeta w = w / Real.sqrt (tiltD w) := by
  have hα := tiltAlpha_sq w
  have hβ := tiltBeta_sq hw
  have hD := tiltD_pos w
  have hs := Real.sq_sqrt hD.le
  have hspos := Real.sqrt_pos.2 hD
  have he : (2*tiltAlpha w*tiltBeta w)^2 * tiltD w = w^2 := by
    calc
      _ = 4*(tiltAlpha w)^2*(tiltBeta w)^2*tiltD w := by ring
      _ = w^2 := by
        rw [hα, hβ]
        have hi := tilt_covariance_identity w
        field_simp
        nlinarith [hi]
  have hh : (w/Real.sqrt (tiltD w))^2*tiltD w=w^2 := by
    rw [div_pow, hs]
    field_simp
  have hp : 0 < 2*tiltAlpha w*tiltBeta w := by
    exact mul_pos (mul_pos (by norm_num) (tiltAlpha_pos w)) (tiltBeta_pos hw)
  have hq : 0 < w/Real.sqrt (tiltD w) := div_pos hw hspos
  exact (sq_eq_sq₀ hp.le hq.le).mp (mul_right_cancel₀ hD.ne' (he.trans hh.symm))

theorem tiltMap_det {w : ℝ} (hw : 0 < w) :
    LinearMap.det (tiltMap w) = 1 / Real.sqrt (tiltD w) := by
  rw [tiltMap, pairLinear_det]
  calc
    _ = (2*tiltAlpha w*tiltBeta w)/w := by ring
    _ = _ := by rw [tiltAlpha_mul_Beta hw]; field_simp

def scalarGaussianPair : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)
def scalarGaussianPairDensity (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / Real.sqrt (2*Real.pi))^2 * Real.exp (-(z.1^2+z.2^2)/2))

instance scalarGaussianPair_probability : IsProbabilityMeasure scalarGaussianPair := by
  unfold scalarGaussianPair
  infer_instance

theorem scalarGaussianPair_eq_withDensity :
    scalarGaussianPair = ((volume : Measure ℝ).prod volume).withDensity
      scalarGaussianPairDensity := by
  unfold scalarGaussianPair
  rw [gaussianReal_of_var_ne_zero _ (one_ne_zero),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  congr 1
  funext z
  dsimp [gaussianPDF, gaussianPDFReal, scalarGaussianPairDensity]
  rw [← ENNReal.ofReal_mul (by positivity)]
  simp only [mul_one, sub_zero]
  congr 1
  calc
    _ = (1 / Real.sqrt (2*Real.pi))^2 *
        (Real.exp (-z.1^2/2)*Real.exp (-z.2^2/2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring


def tiltEquiv (w : ℝ) (hw : 0 < w) : (ℝ × ℝ) ≃ᵐ ℝ × ℝ :=
  pairMeasurableEquiv (tiltAlpha w) (-tiltBeta w)
    ((1-tiltA w)*tiltAlpha w/w) ((1+tiltA w)*tiltBeta w/w) (by
      rw [← pairLinear_det]
      change LinearMap.det (tiltMap w) ≠ 0
      rw [tiltMap_det hw]
      exact div_ne_zero one_ne_zero (Real.sqrt_pos.2 (tiltD_pos w)).ne')

theorem tiltEquiv_apply (w : ℝ) (hw : 0 < w) (z : ℝ × ℝ) :
    tiltEquiv w hw z = tiltMap w z := rfl

theorem measurable_scalarGaussianPairDensity : Measurable scalarGaussianPairDensity := by
  unfold scalarGaussianPairDensity
  fun_prop

@[fun_prop] theorem measurable_scalarVerletWork (w : ℝ) : Measurable (scalarVerletWork w) := by
  unfold scalarVerletWork scalarVerletPosition
  fun_prop

theorem tiltEquiv_map_volume (w : ℝ) (hw : 0 < w) :
    Measure.map (tiltEquiv w hw) ((volume : Measure ℝ).prod volume) =
      ENNReal.ofReal (Real.sqrt (tiltD w)) • ((volume : Measure ℝ).prod volume) := by
  have hd : LinearMap.det (tiltMap w) ≠ 0 := by
    rw [tiltMap_det hw]
    exact div_ne_zero one_ne_zero (Real.sqrt_pos.2 (tiltD_pos w)).ne'
  have hh := Measure.map_linearMap_addHaar_eq_smul_addHaar
    ((volume : Measure ℝ).prod volume) hd
  rw [tiltMap_det hw, one_div, inv_inv, abs_of_pos (Real.sqrt_pos.2 (tiltD_pos w))] at hh
  exact hh

/-- Exact weighted-law identity, including both its normalization and endpoint geometry. -/
theorem scalarGaussian_verlet_tilt_law (w : ℝ) (hw : 0 < w) :
    scalarGaussianPair.withDensity (fun z => ENNReal.ofReal (Real.exp (-scalarVerletWork w z/2))) =
      ENNReal.ofReal (1/Real.sqrt (tiltD w)) • scalarGaussianPair.map (tiltMap w) := by
  let base := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let weight := fun z => ENNReal.ofReal (Real.exp (-scalarVerletWork w z/2))
  have hm : Measurable weight := by dsimp [weight]; fun_prop
  have hmap : scalarGaussianPair.map (tiltMap w) =
      (ENNReal.ofReal (Real.sqrt (tiltD w)) • base).withDensity
        (fun z => scalarGaussianPairDensity ((tiltEquiv w hw).symm z)) := by
    rw [scalarGaussianPair_eq_withDensity]
    have hh := map_density_equiv (tiltEquiv w hw) base scalarGaussianPairDensity
      measurable_scalarGaussianPairDensity
    rw [tiltEquiv_map_volume] at hh
    exact hh
  rw [hmap, withDensity_smul_measure, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (Real.sqrt_pos.2 (tiltD_pos w)).ne',
    ENNReal.ofReal_one, one_smul, scalarGaussianPair_eq_withDensity,
    ← withDensity_mul _ measurable_scalarGaussianPairDensity hm]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨y, rfl⟩ := (tiltEquiv w hw).surjective z
  have hsymm : (tiltEquiv w hw).symm (tiltMap w y) = y :=
    (tiltEquiv w hw).symm_apply_apply y
  simp only [Pi.mul_apply, tiltEquiv_apply]
  rw [hsymm]
  dsimp [scalarGaussianPairDensity, weight]
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
  congr 3
  have hh := tiltMap_quadratic hw y
  linarith

theorem scalarGaussian_verlet_tilt_mass (w : ℝ) (hw : 0 < w) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-scalarVerletWork w z/2)) ∂scalarGaussianPair) =
      ENNReal.ofReal (1/Real.sqrt (tiltD w)) := by
  have hh := congrArg (fun ν : Measure (ℝ × ℝ) => ν univ) (scalarGaussian_verlet_tilt_law w hw)
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, Measure.smul_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ, measure_univ, smul_eq_mul,
    mul_one] at hh
  exact hh


theorem integrable_scalarGaussian_verlet_tilt (w : ℝ) (hw : 0 < w) :
    Integrable (fun z => Real.exp (-scalarVerletWork w z/2)) scalarGaussianPair := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [scalarGaussian_verlet_tilt_mass w hw]
  exact ENNReal.ofReal_lt_top

theorem scalarGaussian_verlet_tilt_expectation (w : ℝ) (hw : 0 < w) :
    (∫ z, Real.exp (-scalarVerletWork w z/2) ∂scalarGaussianPair) =
      1/Real.sqrt (tiltD w) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)) (by fun_prop),
    scalarGaussian_verlet_tilt_mass w hw, ENNReal.toReal_ofReal (by positivity)]

end
end PersistencePays

#print axioms PersistencePays.scalarGaussian_verlet_tilt_law
#print axioms PersistencePays.scalarGaussian_verlet_tilt_mass

#print axioms PersistencePays.scalarGaussian_verlet_tilt_expectation
