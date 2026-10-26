import PersistencePays.EntropyTruncation

/-! Relative entropy as a supremum of bounded measurable exponential tests.
The nonnegative truncated conjugates handle infinite entropy without subtracting
infinite positive and negative logarithmic integrals. -/
open MeasureTheory InformationTheory Real Filter Set
open scoped ENNReal Topology
namespace PersistencePays
noncomputable section
variable {S : Type*} [MeasurableSpace S]

def IsBoundedMeasurable (f : S → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

def entropyDual (μ ν : Measure S) (f : S → ℝ) : ℝ :=
  (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1

lemma IsBoundedMeasurable.integrable {f : S → ℝ} (hf : IsBoundedMeasurable f)
    (μ : Measure S) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C,hC⟩ := hf.2
  apply (integrable_const C).mono' hf.1.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x)

lemma IsBoundedMeasurable.exp_integrable {f : S → ℝ} (hf : IsBoundedMeasurable f)
    (μ : Measure S) [IsFiniteMeasure μ] : Integrable (fun x => exp (f x)) μ := by
  obtain ⟨C,hC⟩ := hf.2
  apply (integrable_const (exp C)).mono' (hf.1.exp.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr ((le_abs_self _).trans (hC x))

theorem entropyDual_le_klDiv (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : IsBoundedMeasurable f) :
    ENNReal.ofReal (entropyDual μ ν f) ≤ klDiv μ ν := by
  by_cases hD : klDiv μ ν = ∞
  · simp [hD]
  obtain ⟨hac,hlog⟩ := klDiv_ne_top_iff.mp hD
  have hkl := (integrable_klFun_rnDeriv_iff hac).mpr hlog
  have hmul := (integrable_toReal_rnDeriv_mul_iff hac).mpr (hf.integrable μ)
  have he := hf.exp_integrable ν
  have hsum : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal + exp (f x)) ν := hkl.add he
  have hi := integral_mono hmul (hsum.sub (integrable_const 1))
    (fun x => mul_le_klFun_add_exp ENNReal.toReal_nonneg (f x))
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  rw [integral_toReal_rnDeriv_mul hac,
    integral_sub hsum (integrable_const 1), integral_add hkl he,
    ← toReal_klDiv_eq_integral_klFun hac] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hh : entropyDual μ ν f ≤ (klDiv μ ν).toReal := by unfold entropyDual; linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_toReal hD)

lemma truncatedLog_boundedMeasurable (μ ν : Measure S) (n : ℕ) :
    IsBoundedMeasurable (fun x => truncatedLog n (μ.rnDeriv ν x).toReal) := by
  refine ⟨(measurable_truncatedLog n).comp (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    (n : ℝ), ?_⟩
  intro x
  exact abs_le.mpr (truncatedLog_bounds _ _)

lemma integral_truncatedDual (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (truncatedDual n (μ.rnDeriv ν x).toReal) ∂ν) =
      ENNReal.ofReal (entropyDual μ ν (fun x => truncatedLog n (μ.rnDeriv ν x).toReal)) := by
  let f : S → ℝ := fun x => truncatedLog n (μ.rnDeriv ν x).toReal
  have hf : IsBoundedMeasurable f := truncatedLog_boundedMeasurable μ ν n
  have hm := (integrable_toReal_rnDeriv_mul_iff hac).mpr (hf.integrable μ)
  have he := hf.exp_integrable ν
  have hi : Integrable (fun x => truncatedDual n (μ.rnDeriv ν x).toReal) ν :=
    (hm.sub he).add (integrable_const 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => truncatedDual_nonneg n ENNReal.toReal_nonneg))]
  congr 1
  have hsub : Integrable (fun x => (μ.rnDeriv ν x).toReal * f x - exp (f x)) ν := hm.sub he
  change (∫ x, (μ.rnDeriv ν x).toReal * f x - exp (f x) + 1 ∂ν) =
    (∫ x, f x ∂μ) - (∫ x, exp (f x) ∂ν) + 1
  rw [integral_add hsub (integrable_const 1), integral_sub hm he,
    integral_toReal_rnDeriv_mul hac]
  simp

/-- The bounded dual tests determine entropy even when it is infinite,
provided absolute continuity holds. -/
theorem klDiv_le_of_bounded_duals_of_ac (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (C : ℝ≥0∞) (hC : ∀ f : S → ℝ, IsBoundedMeasurable f →
      ENNReal.ofReal (entropyDual μ ν f) ≤ C) : klDiv μ ν ≤ C := by
  let F : ℕ → S → ℝ≥0∞ := fun n x => ENNReal.ofReal (truncatedDual n (μ.rnDeriv ν x).toReal)
  have hfm : ∀ n, Measurable (F n) := by
    intro n
    have hh := (truncatedLog_boundedMeasurable μ ν n).1
    exact ENNReal.measurable_ofReal.comp
      ((((Measure.measurable_rnDeriv _ _).ennreal_toReal.mul hh).sub hh.exp).add measurable_const)
  have hlim (x : S) : Tendsto (fun n => F n x) atTop
      (𝓝 (ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (truncatedDual_tendsto ENNReal.toReal_nonneg)
  have hFatou := lintegral_liminf_le (μ:=ν) (u:=atTop) hfm
  have hid : (∫⁻ x, liminf (fun n => F n x) atTop ∂ν) = klDiv μ ν := by
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    exact lintegral_congr (fun x => (hlim x).liminf_eq)
  rw [hid] at hFatou
  apply hFatou.trans
  apply liminf_le_of_frequently_le'
  apply Frequently.of_forall
  intro n
  rw [show (∫⁻ x, F n x ∂ν) = _ from integral_truncatedDual μ ν hac n]
  exact hC _ (truncatedLog_boundedMeasurable μ ν n)

/-- Bounded tests also detect the singular part of a probability law. -/
theorem klDiv_le_of_bounded_duals (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C : ℝ≥0∞) (hC : ∀ f : S → ℝ, IsBoundedMeasurable f →
      ENNReal.ofReal (entropyDual μ ν f) ≤ C) : klDiv μ ν ≤ C := by
  by_cases hac : μ ≪ ν
  · exact klDiv_le_of_bounded_duals_of_ac μ ν hac C hC
  by_cases htop : C = ∞
  · simp [htop]
  obtain ⟨s,hsν,hsμ⟩ : ∃ s : Set S, ν s = 0 ∧ μ s ≠ 0 := by
    simpa only [Measure.AbsolutelyContinuous, not_forall, not_imp, exists_prop] using hac
  let B := toMeasurable ν s
  have hB : MeasurableSet B := measurableSet_toMeasurable _ _
  have hBν : ν B = 0 := by simpa only [B, measure_toMeasurable] using hsν
  have hBμ : μ B ≠ 0 := fun h => hsμ (measure_mono_null (subset_toMeasurable ν s) h)
  have hb : 0 < μ.real B := ENNReal.toReal_pos hBμ (measure_ne_top _ _)
  let R := (C.toReal + 1) / μ.real B
  let f : S → ℝ := B.indicator (fun _ => R)
  have hf : IsBoundedMeasurable f := by
    refine ⟨measurable_const.indicator hB, |R|, ?_⟩
    intro x
    by_cases hx : x ∈ B <;> simp [f,hx]
  have he : (∫ x, exp (f x) ∂ν) = 1 := by
    have ha : (fun x => exp (f x)) =ᵐ[ν] (fun _ => 1) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBν] with x hx
      simp [f,hx]
    rw [integral_congr_ae ha]
    simp
  have hd : entropyDual μ ν f = C.toReal + 1 := by
    unfold entropyDual
    rw [he]
    change (∫ x, B.indicator (fun _ => R) x ∂μ) - 1 + 1 = _
    rw [integral_indicator_const R hB]
    simp only [smul_eq_mul]
    dsimp only [R]
    field_simp
    ring
  have hh := hC f hf
  rw [hd] at hh
  have hr := ENNReal.toReal_mono htop hh
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  linarith

/-- Exact bounded-measurable variational formula for arbitrary probability laws. -/
theorem klDiv_eq_iSup_bounded_dual (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv μ ν = ⨆ (f : S → ℝ) (_ : IsBoundedMeasurable f),
      ENNReal.ofReal (entropyDual μ ν f) := by
  apply le_antisymm
  · exact klDiv_le_of_bounded_duals μ ν _ (fun f hf => le_iSup_of_le f (le_iSup_of_le hf le_rfl))
  · exact iSup_le (fun f => iSup_le (fun hf => entropyDual_le_klDiv μ ν hf))

end
end PersistencePays
#print axioms PersistencePays.klDiv_le_of_bounded_duals_of_ac

#print axioms PersistencePays.klDiv_eq_iSup_bounded_dual
