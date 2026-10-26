import PersistencePays.GaussianBridgeLaw
import PersistencePays.Volume
import PersistencePays.OBABOPath

/-! Explicit triangular density of an actual unadjusted OBABO step. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def triangularNoiseEquiv (a : E) (b : E → E) (hb : Measurable b)
    (α σ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) : (E × E) ≃ᵐ (E × E) where
  toFun η := (a + α • η.1, b (a + α • η.1) + σ • η.2)
  invFun z := (α⁻¹ • (z.1 - a), σ⁻¹ • (z.2 - b z.1))
  left_inv := by intro η; simp [smul_smul, hα, hσ]
  right_inv := by intro z; simp [smul_smul, hα, hσ]
  measurable_toFun := (measurable_const.add (measurable_fst.const_smul α)).prodMk
    ((hb.comp (measurable_const.add (measurable_fst.const_smul α))).add
      (measurable_snd.const_smul σ))
  measurable_invFun := ((measurable_fst.sub_const a).const_smul α⁻¹).prodMk
    ((measurable_snd.sub (hb.comp measurable_fst)).const_smul σ⁻¹)

def triangularInverseJacobian (α σ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|α⁻¹| ^ Module.finrank ℝ E) *
    ENNReal.ofReal (|σ⁻¹| ^ Module.finrank ℝ E)

theorem triangularNoiseEquiv_map_volume (a : E) (b : E → E) (hb : Measurable b)
    (α σ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) :
    Measure.map (triangularNoiseEquiv a b hb α σ hα hσ)
      ((volume : Measure E).prod volume) =
      triangularInverseJacobian (E := E) α σ • ((volume : Measure E).prod volume) := by
  have hs : MeasurePreserving (fun z : E × E => (z.1, b z.1 + z.2))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
    (MeasurePreserving.id volume).skew_product
      ((hb.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall (fun x => (measurePreserving_add_left volume (b x)).map_eq))
  have ha : Measure.map (fun x : E => a + α • x) volume =
      ENNReal.ofReal (|α⁻¹| ^ Module.finrank ℝ E) • volume := by
    change Measure.map ((fun x : E => a + x) ∘ (fun x => α • x)) volume = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_addHaar_smul volume hα, Measure.map_smul,
      (measurePreserving_add_left volume a).map_eq]
    simp [← inv_pow, abs_pow]
  change Measure.map ((fun z : E × E => (z.1, b z.1 + z.2)) ∘
    (Prod.map (fun x : E => a + α • x) (fun x : E => σ • x))) _ = _
  rw [← Measure.map_map hs.measurable (by fun_prop), ← Measure.map_prod_map _ _
    (by fun_prop) (by fun_prop), ha, Measure.map_addHaar_smul volume hσ,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul, hs.map_eq]
  simp [triangularInverseJacobian, ← inv_pow, abs_pow]

def gaussianPairDensity (η : E × E) : ℝ≥0∞ :=
  heatDensity 1 η.1 * heatDensity 1 η.2

theorem measurable_gaussianPairDensity : Measurable (gaussianPairDensity (E := E)) :=
  ((measurable_heatDensity 1).comp measurable_fst).mul
    ((measurable_heatDensity 1).comp measurable_snd)

theorem gaussianPair_eq_density :
    (stdGaussian E).prod (stdGaussian E) =
      ((volume : Measure E).prod volume).withDensity gaussianPairDensity := by
  rw [stdGaussian_eq_heatDensity, prod_withDensity
    (measurable_heatDensity 1) (measurable_heatDensity 1)]
  rfl

theorem triangularNoiseEquiv_density (a : E) (b : E → E) (hb : Measurable b)
    (α σ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0) :
    Measure.map (triangularNoiseEquiv a b hb α σ hα hσ)
      ((stdGaussian E).prod (stdGaussian E)) =
      ((volume : Measure E).prod volume).withDensity (fun z =>
        triangularInverseJacobian (E := E) α σ *
          gaussianPairDensity ((triangularNoiseEquiv a b hb α σ hα hσ).symm z)) := by
  have hm : Measurable (fun z => gaussianPairDensity
      ((triangularNoiseEquiv a b hb α σ hα hσ).symm z)) :=
    measurable_gaussianPairDensity.comp (triangularNoiseEquiv a b hb α σ hα hσ).symm.measurable
  rw [gaussianPair_eq_density, map_density_equiv _ _ _ measurable_gaussianPairDensity,
    triangularNoiseEquiv_map_volume, withDensity_smul_measure, ← withDensity_smul _ hm]
  rfl


def obaboNoiseEquiv (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (hh : h ≠ 0) (hσ : σ ≠ 0) (z : E × E) : (E × E) ≃ᵐ (E × E) :=
  triangularNoiseEquiv (z.1 + (h*r) • z.2 - (h^2/2) • g z.1)
    (fun y => r • (h⁻¹ • (y-z.1) - (h/2) • g y))
    (by fun_prop) (h*σ) σ (mul_ne_zero hh hσ) hσ

theorem obaboNoiseEquiv_apply (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (hh : h ≠ 0) (hσ : σ ≠ 0) (z η : E × E) :
    obaboNoiseEquiv g hg h r σ hh hσ z η =
      OBABOPath.ou r σ η.2 (verlet g h (OBABOPath.ou r σ η.1 z)) := by
  have hx : z.1 + (h*r) • z.2 - (h^2/2) • g z.1 + (h*σ) • η.1 =
      z.1 + h • (r • z.2 + σ • η.1 - (h/2) • g z.1) := by module
  have hv : h⁻¹ • (z.1 + h • (r • z.2 + σ • η.1 - (h/2) • g z.1) - z.1) =
      r • z.2 + σ • η.1 - (h/2) • g z.1 := by
    simp [smul_smul, hh]
  simp only [obaboNoiseEquiv, triangularNoiseEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
    OBABOPath.ou, verlet, kick, drift, hx, hv]

theorem gaussianPairDensity_le (η : E × E) :
    gaussianPairDensity η ≤ ENNReal.ofReal (heatConstant E 1 ^ 2) := by
  have h (x : E) : heatReal 1 x ≤ heatConstant E 1 := by
    unfold heatReal
    apply mul_le_of_le_one_right (heatConstant_pos (E := E) (by norm_num)).le
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  unfold gaussianPairDensity heatDensity
  calc
    _ ≤ ENNReal.ofReal (heatConstant E 1) * ENNReal.ofReal (heatConstant E 1) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (h η.1)) (ENNReal.ofReal_le_ofReal (h η.2))
    _ = _ := by rw [← ENNReal.ofReal_mul (heatConstant_pos (E := E) (by norm_num)).le]; congr 1; ring

theorem obabo_one_step_density (g : E → E) (hg : Measurable g) (h r σ : ℝ)
    (hh : h ≠ 0) (hσ : σ ≠ 0) (z : E × E) :
    Measure.map (fun η : E × E => OBABOPath.ou r σ η.2
      (verlet g h (OBABOPath.ou r σ η.1 z))) ((stdGaussian E).prod (stdGaussian E)) =
      ((volume : Measure E).prod volume).withDensity (fun w =>
        triangularInverseJacobian (E := E) (h*σ) σ *
          gaussianPairDensity ((obaboNoiseEquiv g hg h r σ hh hσ z).symm w)) := by
  have he : (fun η : E × E => OBABOPath.ou r σ η.2
      (verlet g h (OBABOPath.ou r σ η.1 z))) = obaboNoiseEquiv g hg h r σ hh hσ z := by
    funext η
    exact (obaboNoiseEquiv_apply g hg h r σ hh hσ z η).symm
  rw [he]
  exact triangularNoiseEquiv_density _ _ _ _ _ _ _

end PersistencePays
#print axioms PersistencePays.triangularNoiseEquiv_density
