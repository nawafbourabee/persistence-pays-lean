import PersistencePays.Assumptions
import PersistencePays.GibbsProduct
import PersistencePays.GaussianBridgeLaw

/-! Actual diagonal Gaussian Gibbs laws and the independent-coordinate representation. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal InnerProductSpace

/-- Tilting commutes with an invertible measurable change of variables. -/
theorem map_tilted_equiv {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (e : S ≃ᵐ T) (μ : Measure S) (f : S → ℝ) (hf : Measurable f) :
    (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  have he : (∫ y, Real.exp (f (e.symm y)) ∂μ.map e) = ∫ x, Real.exp (f x) ∂μ := by
    have hh := integral_map e.measurable.aemeasurable
      ((hf.comp e.symm.measurable).exp.aestronglyMeasurable (μ := μ.map e))
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hh
  rw [Measure.tilted, Measure.tilted, map_density_equiv e μ _ (by fun_prop), he]

theorem tilted_smul_positive {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (c : ℝ) (hc : 0 < c) (f : S → ℝ) (hf : Measurable f) :
    (ENNReal.ofReal c • μ).tilted f = μ.tilted f := by
  rw [Measure.tilted, Measure.tilted, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal c) (by fun_prop)]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hc.le]
  congr 1
  by_cases hZ : (∫ x, Real.exp (f x) ∂μ) = 0
  · simp [hZ]
  · field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem linear_image_standardGaussian_gibbs (e : E ≃L[ℝ] E) :
    (stdGaussian E).map e =
      (volume : Measure E).tilted (fun x => -kineticPotential (e.symm x)) := by
  rw [stdGaussian_eq_kinetic_tilted]
  have hm := map_tilted_equiv e.toHomeomorph.toMeasurableEquiv
    (volume : Measure E) (-kineticPotential) (by unfold kineticPotential; fun_prop)
  change Measure.map e (volume.tilted (-kineticPotential)) = _
  change Measure.map e (volume.tilted (-kineticPotential)) =
    (Measure.map e volume).tilted (fun x => -kineticPotential (e.symm x)) at hm
  rw [hm]
  change (Measure.map e volume).tilted (fun x => -kineticPotential (e.symm x)) = _
  rw [map_volume_linearEquiv]
  unfold inverseJacobian
  apply tilted_smul_positive
  · exact abs_pos.mpr (inv_ne_zero e.toLinearEquiv.isUnit_det'.ne_zero)
  · unfold kineticPotential
    fun_prop

variable {ι : Type*} [Fintype ι]

def diagonalLinear (a : ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => a i*x i)
  map_add' := by intro x y; ext i; simp; ring
  map_smul' := by intro c x; ext i; simp; ring

def diagonalEquiv (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  (show EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι from
    { toLinearMap := diagonalLinear a
      invFun := fun x => WithLp.toLp 2 (fun i => (a i)⁻¹*x i)
      left_inv := by intro x; ext i; simp [diagonalLinear, ha, mul_assoc]
      right_inv := by intro x; ext i; simp [diagonalLinear, ha, mul_assoc] }).toContinuousLinearEquiv

def diagonalPotential (a : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (∑ i, a i*(x i)^2)/2

def gaussianPositionMap (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  diagonalEquiv (fun i => (Real.sqrt (a i))⁻¹)
    (fun i => inv_ne_zero (Real.sqrt_pos.2 (ha i)).ne')

theorem diagonalLinear_apply (a : ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    diagonalLinear a x i = a i*x i := rfl

theorem gaussianPositionMap_apply (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    gaussianPositionMap a ha x i = x i / Real.sqrt (a i) := by
  change (Real.sqrt (a i))⁻¹*x i = _
  ring

theorem diagonalPotential_kinetic (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (x : EuclideanSpace ℝ ι) :
    diagonalPotential a x = kineticPotential ((gaussianPositionMap a ha).symm x) := by
  rw [diagonalPotential, kineticPotential, EuclideanSpace.real_norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change a i*(x i)^2 = ((Real.sqrt (a i))⁻¹⁻¹*x i)^2
  rw [inv_inv, mul_pow, Real.sq_sqrt (ha i).le]

theorem diagonal_positionGibbs (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    positionGibbs (diagonalPotential a) =
      (stdGaussian (EuclideanSpace ℝ ι)).map (gaussianPositionMap a ha) := by
  rw [linear_image_standardGaussian_gibbs]
  unfold positionGibbs
  congr 1
  funext x
  exact congrArg Neg.neg (diagonalPotential_kinetic a ha x)


theorem diagonalLinear_symmetric (a : ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    ⟪diagonalLinear a x, y⟫_ℝ = ⟪x, diagonalLinear a y⟫_ℝ := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
    conj_trivial, diagonalLinear_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonalPotential_quadratic (a : ι → ℝ) :
    diagonalPotential a = quadraticPotential (diagonalLinear a) 0 0 := by
  funext x
  simp only [diagonalPotential, quadraticPotential, inner_zero_left, add_zero, PiLp.inner_apply,
    real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, diagonalLinear_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonalPotential_hasGradientAt (a : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    HasGradientAt (diagonalPotential a) (diagonalLinear a x) x := by
  rw [diagonalPotential_quadratic]
  simpa using quadratic_hasGradientAt (diagonalLinear a).toContinuousLinearMap 0 0
    (diagonalLinear_symmetric a) x

theorem diagonalPotential_gradient (a : ι → ℝ) :
    gradient (diagonalPotential a) = diagonalLinear a :=
  gradient_eq (diagonalPotential_hasGradientAt a)

def standardPairCoordinates (z : ι → ℝ × ℝ) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  (WithLp.toLp 2 (fun i => (z i).1), WithLp.toLp 2 (fun i => (z i).2))

theorem standardPairCoordinates_law :
    (Measure.pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))).map
      standardPairCoordinates =
      (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hregroup := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).map_eq
  have hstd := Measure.map_prod_map
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) (Measure.pi (fun _ : ι => gaussianReal 0 1))
    (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
    (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
  rw [map_pi_eq_stdGaussian] at hstd
  rw [hstd, ← hregroup, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

def diagonalPhaseMap (a : ι → ℝ) (z : ι → ℝ × ℝ) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  (WithLp.toLp 2 (fun i => (z i).1/Real.sqrt (a i)), WithLp.toLp 2 (fun i => (z i).2))

@[fun_prop] theorem diagonalPhaseMap_measurable (a : ι → ℝ) :
    Measurable (diagonalPhaseMap a) := by
  unfold diagonalPhaseMap
  fun_prop

/-- Actual product-coordinate representation of the stationary phase-space law. -/
theorem diagonal_phaseGibbs (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    phaseGibbs (diagonalPotential a) =
      (Measure.pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))).map
        (diagonalPhaseMap a) := by
  unfold phaseGibbs
  rw [diagonal_positionGibbs a ha]
  have hh := Measure.map_prod_map (stdGaussian (EuclideanSpace ℝ ι))
    (stdGaussian (EuclideanSpace ℝ ι)) (gaussianPositionMap a ha).continuous.measurable measurable_id
  rw [Measure.map_id] at hh
  rw [hh, ← standardPairCoordinates_law, Measure.map_map (by fun_prop) (by unfold standardPairCoordinates; fun_prop)]
  congr 1
  funext z
  apply Prod.ext
  · ext i
    exact gaussianPositionMap_apply a ha (standardPairCoordinates z).1 i
  · rfl


theorem diagonalPotential_hessian (a : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    hessian (diagonalPotential a) x = (diagonalLinear a).toContinuousLinearMap := by
  unfold hessian
  rw [diagonalPotential_gradient]
  exact (diagonalLinear a).toContinuousLinearMap.hasFDerivAt.fderiv

theorem diagonalPotential_hessian_form (a : ι → ℝ) (x u : EuclideanSpace ℝ ι) :
    ⟪hessian (diagonalPotential a) x u, u⟫_ℝ = ∑ i, a i*(u i)^2 := by
  rw [diagonalPotential_hessian]
  change ⟪diagonalLinear a u, u⟫_ℝ = _
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, diagonalLinear_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonalPotential_A1 (a : ι → ℝ) (m L : ℝ) (hm : 0 < m) (hmL : m ≤ L)
    (hal : ∀ i, m ≤ a i) (hau : ∀ i, a i ≤ L) : A1 (diagonalPotential a) m L where
  twice_contDiff := by unfold diagonalPotential; fun_prop
  m_pos := hm
  m_le_L := hmL
  lower := by
    intro x u
    rw [diagonalPotential_hessian_form, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hal i) (sq_nonneg _))
  upper := by
    intro x u
    rw [diagonalPotential_hessian_form, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hau i) (sq_nonneg _))

theorem diagonalPotential_A2 (a : ι → ℝ) : A2 (diagonalPotential a) 0 where
  lipschitz := by intro x y; rw [diagonalPotential_hessian, diagonalPotential_hessian]; simp

end
end PersistencePays

#print axioms PersistencePays.diagonalPotential_gradient
#print axioms PersistencePays.diagonal_phaseGibbs

#print axioms PersistencePays.diagonalPotential_A1
