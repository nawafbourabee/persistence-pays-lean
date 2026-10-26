import PersistencePays.EpochRejectionBound

/-! Gaussian crossing bounds used in Appendix B. -/

noncomputable section
namespace PersistencePays.GaussianLowerBound

open MeasureTheory ProbabilityTheory Set

theorem standard_normal_pdf_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / 2 := by
  have hs : 2 ≤ Real.sqrt (2 * Real.pi) := by
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    have hsquare := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
    have hnonneg := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith
  have hi : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  have he : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  calc
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      simp [gaussianPDFReal]
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 / 2 := by simpa using hi

theorem standard_normal_interval_bound (a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 1).real (Icc (-a) a) ≤ a := by
  have hi : IntegrableOn (gaussianPDFReal 0 1) (Icc (-a) a) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc (-a) a) := by
    exact integrableOn_const (by simp)
  have hm : (∫ x in Icc (-a) a, gaussianPDFReal 0 1 x) ≤
      ∫ _ : ℝ in Icc (-a) a, (1 / 2 : ℝ) :=
    integral_mono hi hc (standard_normal_pdf_le_half)
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _))]
  calc
    _ ≤ _ := hm
    _ = a := by
      simp [sub_neg_eq_add]
      rw [max_eq_left (by linarith : 0 ≤ a + a)]
      ring

theorem standard_normal_abs_mean_le_one : (∫ x, |x| ∂gaussianReal 0 1) ≤ 1 := by
  have hid : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have habs : MemLp (fun x : ℝ => |x|) 2 (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs] using hid.norm
  have hsq : (∫ x, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have hh := variance_eq_sub hid
    simpa only [variance_fun_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      Pi.pow_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using hh.symm
  have hv := variance_nonneg (X := fun x : ℝ => |x|) (μ := gaussianReal 0 1)
  rw [variance_eq_sub habs] at hv
  simp only [Pi.pow_apply, sq_abs, hsq] at hv
  have hn : 0 ≤ ∫ x, |x| ∂gaussianReal 0 1 := integral_nonneg (fun _ => abs_nonneg _)
  nlinarith

theorem standard_normal_positive_mean_le_half :
    (∫ x, max x 0 ∂gaussianReal 0 1) ≤ 1 / 2 := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have he := integral_abs_eq_two_mul_integral_posPart_sub_integral hid
  simp only [integral_id_gaussianReal, sub_zero, PosPart.posPart] at he
  nlinarith [standard_normal_abs_mean_le_one]

/-- A Gaussian wedge bound sufficient for the paper's exact crossing
constant. This avoids assuming an unformalized Gaussian quadrant formula. -/
theorem standard_normal_wedge_bound (t : ℝ) (ht : 0 ≤ t) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | p.1 ≤ t * p.2 ∧ -t * p.2 < p.1} ≤ t / 2 := by
  let A : Set (ℝ × ℝ) := {p | p.1 ≤ t * p.2 ∧ -t * p.2 < p.1}
  have hA : MeasurableSet A := by
    change MeasurableSet ({p : ℝ × ℝ | p.1 ≤ t * p.2} ∩ {p | -t * p.2 < p.1})
    exact (measurableSet_le measurable_fst (measurable_snd.const_mul t)).inter
      (measurableSet_lt (measurable_snd.const_mul (-t)) measurable_fst)
  have hm : Measurable (fun y : ℝ => ((gaussianReal 0 1)
      ((fun x : ℝ => (x, y)) ⁻¹' A)).toReal) :=
    (measurable_measure_prodMk_right hA).ennreal_toReal
  have hb (y : ℝ) : (gaussianReal 0 1).real ((fun x : ℝ => (x, y)) ⁻¹' A) ≤ t * max y 0 := by
    calc
      _ ≤ (gaussianReal 0 1).real (Icc (-(t * max y 0)) (t * max y 0)) := by
        apply measureReal_mono _ (by finiteness)
        intro x hx
        have hxy : x ≤ t * y ∧ -t * y < x := hx
        have hmy := mul_le_mul_of_nonneg_left (le_max_left y 0) ht
        constructor <;> linarith
      _ ≤ _ := standard_normal_interval_bound _ (mul_nonneg ht (le_max_right y 0))
  have hi : Integrable (fun y : ℝ => ((gaussianReal 0 1)
      ((fun x : ℝ => (x, y)) ⁻¹' A)).toReal) (gaussianReal 0 1) := by
    apply OBABOPath.integrable_unit_bounded _ _ hm
    · intro y; positivity
    · intro y; exact measureReal_le_one
  have hid : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hip : Integrable (fun y : ℝ => t * max y 0) (gaussianReal 0 1) :=
    (hid.sup (integrable_const 0)).const_mul t
  change (((gaussianReal 0 1).prod (gaussianReal 0 1)) A).toReal ≤ _
  rw [Measure.prod_apply_symm hA,
    ← integral_toReal (measurable_measure_prodMk_right hA).aemeasurable
      (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _))]
  calc
    _ ≤ ∫ y, t * max y 0 ∂gaussianReal 0 1 := integral_mono hi hip hb
    _ = t * (∫ y, max y 0 ∂gaussianReal 0 1) := integral_const_mul _ _
    _ ≤ t * (1 / 2) := mul_le_mul_of_nonneg_left standard_normal_positive_mean_le_half ht
    _ = t / 2 := by ring

end PersistencePays.GaussianLowerBound

#print axioms PersistencePays.GaussianLowerBound.standard_normal_wedge_bound
