import PersistencePays.GibbsIntegrationByParts
import PersistencePays.RadialCutoff

/-! Passing an actual compact-test distributional divergence bound to the
Gibbs law. Global integrability of the nonnegative divergence is a conclusion,
not an added assumption. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gibbsCutoffTest (U:E→ℝ) (n:ℕ) (x:E) : ℝ :=
  radialCutoff n x*Real.exp (-U x)

theorem A1.gibbsCutoffTest_contDiff {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (n:ℕ) :
    ContDiff ℝ 1 (gibbsCutoffTest U n) :=
  ((radialCutoff_contDiff n).of_le (by norm_num)).mul
    ((a.twice_contDiff.of_le (by norm_num)).neg.exp)

theorem gibbsCutoffTest_compact (U:E→ℝ) (n:ℕ) : HasCompactSupport (gibbsCutoffTest U n) :=
  (radialCutoff_compact n).mul_right

theorem gibbsCutoffTest_nonneg (U:E→ℝ) (n:ℕ) (x:E) : 0≤gibbsCutoffTest U n x :=
  mul_nonneg (radialCutoff_mem_Icc n x).1 (Real.exp_nonneg _)

theorem A1.gibbsCutoffTest_fderiv {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (n:ℕ) (x v:E) :
    fderiv ℝ (gibbsCutoffTest U n) x v =
      Real.exp (-U x)*((fderiv ℝ (radialCutoff n) x) v-
        radialCutoff n x*⟪gradient U x,v⟫_ℝ) := by
  unfold gibbsCutoffTest
  have hw : DifferentiableAt ℝ (fun y => Real.exp (-U y)) x :=
    (a.hasGradientAt x).hasFDerivAt.neg.exp.differentiableAt
  rw [fderiv_fun_mul ((radialCutoff_contDiff n).differentiable (by simp) x) hw]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [a.gibbs_weight_fderiv]
  ring

theorem A1.gibbs_divergence_from_compact {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (T:E→E) (hT:MemLp T 2 (positionGibbs U)) (q:E→ℝ) (hq:Measurable q)
    (hq0:∀ᵐ x ∂(volume:Measure E),0≤q x)
    (hcompact:∀ η:E→ℝ,ContDiff ℝ 1 η → HasCompactSupport η → (∀ x,0≤η x) →
      Integrable (fun x => η x*q x) volume ∧
        (∫ x,η x*q x)≤-(∫ x,(fderiv ℝ η x) (T x))) :
    Integrable q (positionGibbs U) ∧
      (∫ x,q x ∂positionGibbs U)≤∫ x,⟪gradient U x,T x⟫_ℝ ∂positionGibbs U := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hTi := hT.integrable (by norm_num)
  have hforce : Integrable (fun x => ⟪gradient U x,T x⟫_ℝ) (positionGibbs U) :=
    integrable_inner_of_memLp_two (a.gradient_memLp a.position_memLp_two) hT
  have hc (n:ℕ) := hcompact (gibbsCutoffTest U n) (a.gibbsCutoffTest_contDiff n)
    (gibbsCutoffTest_compact U n) (gibbsCutoffTest_nonneg U n)
  have hi (n:ℕ) : Integrable (fun x => radialCutoff n x*q x) (positionGibbs U) := by
    apply (a.gibbs_integrable_iff_weighted _).mpr
    convert (hc n).1 using 1
    funext x
    unfold gibbsCutoffTest
    ring
  have hloc (n:ℕ) : (∫ x,radialCutoff n x*q x ∂positionGibbs U) ≤
      (∫ x,radialCutoff n x*⟪gradient U x,T x⟫_ℝ ∂positionGibbs U)-
        (∫ x,(fderiv ℝ (radialCutoff n) x) (T x) ∂positionGibbs U) := by
    have hfi := radialCutoff_mul_integrable hforce n
    have hei := radialCutoff_derivative_integrable hTi n
    have hfw := (a.gibbs_integrable_iff_weighted _).mp hfi
    have hew := (a.gibbs_integrable_iff_weighted _).mp hei
    have heq : (∫ x,(fderiv ℝ (gibbsCutoffTest U n) x) (T x)) =
        (∫ x,((fderiv ℝ (radialCutoff n) x) (T x))*Real.exp (-U x))-
          (∫ x,(radialCutoff n x*⟪gradient U x,T x⟫_ℝ)*Real.exp (-U x)) := by
      rw [← integral_sub hew hfw]
      apply integral_congr_ae
      filter_upwards with x
      rw [a.gibbsCutoffTest_fderiv]
      ring
    have hh := div_le_div_of_nonneg_right (hc n).2 a.gibbs_normalizer_pos.le
    rw [heq] at hh
    rw [gibbs_integral_weighted,gibbs_integral_weighted,gibbs_integral_weighted]
    have heq' : (∫ x,radialCutoff n x*q x*Real.exp (-U x)) =
        ∫ x,gibbsCutoffTest U n x*q x := by
      apply integral_congr_ae
      filter_upwards with x
      unfold gibbsCutoffTest
      ring
    rw [heq']
    simpa only [neg_sub,sub_div] using hh
  have hqμ : ∀ᵐ x ∂positionGibbs U,0≤q x :=
    (tilted_absolutelyContinuous volume (-U)).ae_le hq0
  apply integral_bound_of_cutoffs (μ:=positionGibbs U) hq.aestronglyMeasurable hqμ hforce
    (fun n => (radialCutoff_contDiff n).continuous.aestronglyMeasurable)
    (fun n => .of_forall (radialCutoff_mem_Icc n))
    (.of_forall radialCutoff_tendsto) hi
    (by simpa only [neg_zero] using (radialCutoff_derivative_error hTi).neg)
  intro n
  simpa only [sub_eq_add_neg] using hloc n

end PersistencePays
#print axioms PersistencePays.A1.gibbs_divergence_from_compact
