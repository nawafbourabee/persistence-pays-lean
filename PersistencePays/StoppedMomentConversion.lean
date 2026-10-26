import PersistencePays.LyapunovDrift
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Exponential stopped moments imply the polynomial moments of Lemma 5.6(ii).
The proof first obtains a second moment, then uses Hölder for every exponent up to two. -/
namespace PersistencePays
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A scalar inequality giving a polynomial moment from a shifted exponential. -/
theorem square_le_shifted_exp (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) :
    y^2 ≤ a^2+2*(a+1)*Real.exp (y-a) := by
  by_cases hya : y ≤ a
  · have hn := Real.exp_nonneg (y-a)
    nlinarith [mul_nonneg (show 0 ≤ a+1 by positivity) hn]
  · have ht : 0 ≤ y-a := by linarith
    have hl := Real.add_one_le_exp (y-a)
    have hq := Real.quadratic_le_exp_of_nonneg ht
    have hmul := mul_le_mul_of_nonneg_left hl ha
    nlinarith

/-- Hölder on a subprobability measure, with no moment or finiteness assumption hidden. -/
theorem lintegral_rpow_le_second_moment (ν : Measure Ω) (hmass : ν univ ≤ 1)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (ω : ℝ) (hω : 0 ≤ ω) (hωmax : ω ≤ 2) :
    (∫⁻ x, f x^ω ∂ν) ≤ (∫⁻ x, (f x)^2 ∂ν)^(ω/2) := by
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := fun x => (f x)^2) (g := fun _ => (1:ℝ≥0∞))
    (hf.pow_const 2).aemeasurable aemeasurable_const
    (show 0 ≤ ω/2 by positivity) (show 0 ≤ 1-ω/2 by linarith)
    (show ω/2+(1-ω/2)=1 by ring)
  have he (x : Ω) : ((f x)^2)^(ω/2) = f x^ω := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    congr 1
    ring
  simp only [he, ENNReal.one_rpow, mul_one, lintegral_const, one_mul] at hh
  calc
    _ ≤ (∫⁻ x, (f x)^2 ∂ν)^(ω/2)*(ν univ)^(1-ω/2) := hh
    _ ≤ (∫⁻ x, (f x)^2 ∂ν)^(ω/2)*1 :=
      mul_le_mul' le_rfl ((ENNReal.rpow_le_rpow hmass (by linarith)).trans_eq (ENNReal.one_rpow _))
    _ = _ := mul_one _

/-- A bounded stopped exponential moment yields a second moment with a fixed additive cost. -/
theorem exponential_second_moment (ν : Measure Ω) (hmass : ν univ ≤ 1)
    (V : Ω → ℝ) (hV : Measurable V) (hVpos : ∀ x, 0 ≤ V x)
    (Q0 : ℝ) (hQ : 0 ≤ Q0)
    (hmgf : (∫⁻ x, ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*Q0))) :
    (∫⁻ x, ENNReal.ofReal ((V x)^2) ∂ν) ≤ ENNReal.ofReal ((Q0+40)^2) := by
  let a : ℝ := (1/20:ℝ)*Q0
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hmexp : Measurable (fun x => ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x))) := by fun_prop
  have hshift : (∫⁻ x, ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x-a)) ∂ν) ≤ 1 := by
    have he (x : Ω) : Real.exp ((1/20:ℝ)*V x-a) = Real.exp ((1/20:ℝ)*V x)*Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
    simp_rw [he, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [lintegral_mul_const _ hmexp]
    calc
      _ ≤ ENNReal.ofReal (Real.exp a)*ENNReal.ofReal (Real.exp (-a)) := mul_le_mul' hmgf le_rfl
      _ = 1 := by rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]; simp
  have hpoint (x : Ω) : (V x)^2 ≤ 400*(a^2+2*(a+1)*Real.exp ((1/20:ℝ)*V x-a)) := by
    have hb := square_le_shifted_exp a ((1/20:ℝ)*V x) ha (mul_nonneg (by norm_num) (hVpos x))
    nlinarith
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (400*(a^2+2*(a+1)*Real.exp ((1/20:ℝ)*V x-a))) ∂ν :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hpoint x))
    _ = ENNReal.ofReal 400 * (ENNReal.ofReal (a^2)*ν univ+
        ENNReal.ofReal (2*(a+1))*(∫⁻ x, ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x-a)) ∂ν)) := by
      have he (x : Ω) : ENNReal.ofReal (a^2+2*(a+1)*Real.exp ((1/20:ℝ)*V x-a)) =
          ENNReal.ofReal (a^2)+ENNReal.ofReal (2*(a+1))*ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x-a)) := by
        rw [ENNReal.ofReal_add (sq_nonneg a)
          (show 0 ≤ 2*(a+1)*Real.exp ((1/20:ℝ)*V x-a) by positivity),
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*(a+1))]
      simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 400), he]
      rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left measurable_const,
        lintegral_const, lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal 400*(ENNReal.ofReal (a^2)*1+ENNReal.ofReal (2*(a+1))*1) := by gcongr
    _ ≤ ENNReal.ofReal ((Q0+40)^2) := by
      rw [mul_one, mul_one, ← ENNReal.ofReal_add (sq_nonneg a) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 400)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [a]
      nlinarith

/-- The stated polynomial-moment constant of Lemma 5.6(ii), in fact valid for
all exponents in `[0,2]`. The measure may be a killed/subprobability law. -/
theorem stopped_energy_moment_lintegral (ν : Measure Ω) (hmass : ν univ ≤ 1)
    (H V : Ω → ℝ) (hH : Measurable H) (hV : Measurable V)
    (hHpos : ∀ x, 0 ≤ H x) (hVH : ∀ x, (0.79:ℝ)*H x ≤ V x)
    (Q0 : ℝ) (hQ : 0 ≤ Q0)
    (hmgf : (∫⁻ x, ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*Q0)))
    (ω : ℝ) (hω : 0 ≤ ω) (hωmax : ω ≤ 2) :
    (∫⁻ x, ENNReal.ofReal ((H x)^ω) ∂ν) ≤ ENNReal.ofReal (((1.266:ℝ)*(Q0+50))^ω) := by
  have hVpos (x : Ω) : 0 ≤ V x := (mul_nonneg (by norm_num) (hHpos x)).trans (hVH x)
  have hv2 := exponential_second_moment ν hmass V hV hVpos Q0 hQ hmgf
  have hh2 : (∫⁻ x, ENNReal.ofReal ((H x)^2) ∂ν) ≤
      ENNReal.ofReal (((1.266:ℝ)*(Q0+50))^2) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((100/79:ℝ)^2)*ENNReal.ofReal ((V x)^2) ∂ν := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_self_le_mul_self (mul_nonneg (by norm_num : (0:ℝ) ≤ 0.79) (hHpos x)) (hVH x)
        nlinarith
      _ = ENNReal.ofReal ((100/79:ℝ)^2)*(∫⁻ x, ENNReal.ofReal ((V x)^2) ∂ν) :=
        lintegral_const_mul _ (by fun_prop)
      _ ≤ ENNReal.ofReal ((100/79:ℝ)^2)*ENNReal.ofReal ((Q0+40)^2) := mul_le_mul' le_rfl hv2
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg Q0]
  have hp := lintegral_rpow_le_second_moment ν hmass (fun x => ENNReal.ofReal (H x))
    hH.ennreal_ofReal ω hω hωmax
  have hC : 0 ≤ (1.266:ℝ)*(Q0+50) := by positivity
  have heω (x : Ω) := ENNReal.ofReal_rpow_of_nonneg (hHpos x) hω
  have he2 (x : Ω) := ENNReal.ofReal_pow (hHpos x) 2
  simp only [heω, ← he2] at hp
  apply hp.trans
  calc
    _ ≤ (ENNReal.ofReal (((1.266:ℝ)*(Q0+50))^2))^(ω/2) :=
      ENNReal.rpow_le_rpow hh2 (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_pow hC, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      have he : (2:ℝ)*(ω/2)=ω := by ring
      rw [he, ENNReal.ofReal_rpow_of_nonneg hC hω]

/-- Real-valued moments and their integrability, so no Bochner-integral convention
can hide a divergent moment. -/
theorem stopped_energy_moment (ν : Measure Ω) (hmass : ν univ ≤ 1)
    (H V : Ω → ℝ) (hH : Measurable H) (hV : Measurable V)
    (hHpos : ∀ x, 0 ≤ H x) (hVH : ∀ x, (0.79:ℝ)*H x ≤ V x)
    (Q0 : ℝ) (hQ : 0 ≤ Q0)
    (hmgf : (∫⁻ x, ENNReal.ofReal (Real.exp ((1/20:ℝ)*V x)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((1/20:ℝ)*Q0)))
    (ω : ℝ) (hω : 0 ≤ ω) (hωmax : ω ≤ 2) :
    Integrable (fun x => (H x)^ω) ν ∧ (∫ x, (H x)^ω ∂ν) ≤ ((1.266:ℝ)*(Q0+50))^ω := by
  have hb := stopped_energy_moment_lintegral ν hmass H V hH hV hHpos hVH Q0 hQ hmgf ω hω hωmax
  have hm : Measurable (fun x => (H x)^ω) := hH.pow_const ω
  have hn (x : Ω) : 0 ≤ (H x)^ω := Real.rpow_nonneg (hHpos x) _
  constructor
  · refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    have hright : 0 ≤ ((1.266:ℝ)*(Q0+50))^ω := Real.rpow_nonneg (by positivity) _
    rw [ENNReal.toReal_ofReal hright] at ht
    exact ht

end
end PersistencePays
#print axioms PersistencePays.exponential_second_moment

#print axioms PersistencePays.stopped_energy_moment
