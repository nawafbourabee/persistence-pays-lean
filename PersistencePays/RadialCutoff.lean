import PersistencePays.CutoffIntegration
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit smooth radial cutoffs tending to one, with vanishing derivative
errors against every actual integrable vector field. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def radialBase : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩

def radialCutoff (n : ℕ) (x : E) : ℝ := (radialBase (E:=E)) ((1/((n:ℝ)+1)) • x)

theorem radialCutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (radialCutoff (E:=E) n) := by
  exact (radialBase (E:=E)).contDiff.comp (contDiff_const.smul contDiff_id)

theorem radialCutoff_compact (n : ℕ) : HasCompactSupport (radialCutoff (E:=E) n) :=
  (radialBase (E:=E)).hasCompactSupport.comp_smul (by positivity)

theorem radialCutoff_mem_Icc (n : ℕ) (x:E) : radialCutoff n x∈Set.Icc (0:ℝ) 1 :=
  ⟨(radialBase (E:=E)).nonneg,(radialBase (E:=E)).le_one⟩

theorem radialCutoff_tendsto (x:E) : Tendsto (fun n => radialCutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n:ℕ => (1/((n:ℝ)+1)) • x) atTop (𝓝 (0:E)) := by
    simpa only [zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).smul_const x
  have hb : (radialBase (E:=E)) (0:E)=1 :=
    (radialBase (E:=E)).one_of_mem_closedBall (by simp [radialBase])
  have hh := (radialBase (E:=E)).continuous.tendsto 0 |>.comp ht
  rw [hb] at hh
  exact hh

theorem radialCutoff_fderiv_bound : ∃ C:ℝ,0≤C ∧
    ∀ (n:ℕ) (x:E),‖fderiv ℝ (radialCutoff n) x‖≤C/((n:ℝ)+1) := by
  have hc : Continuous (fderiv ℝ (radialBase (E:=E))) :=
    (radialBase (E:=E)).contDiff (n:=1) |>.continuous_fderiv (by simp)
  have hh : HasCompactSupport (fun x:E => ‖fderiv ℝ (radialBase (E:=E)) x‖) :=
    (radialBase (E:=E)).hasCompactSupport.fderiv (𝕜:=ℝ) |>.comp_left norm_zero
  obtain ⟨R,hR⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hh
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro n x
  let s : ℝ := 1/((n:ℝ)+1)
  have hs : 0≤s := by dsimp [s]; positivity
  have hd := ((radialBase (E:=E)).contDiff (n:=1) |>.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s)
  have hd' : HasFDerivAt (radialCutoff (E:=E) n)
      ((fderiv ℝ (radialBase (E:=E)) (s • x)).comp (s • ContinuousLinearMap.id ℝ E)) x := hd
  rw [hd'.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (radialBase (E:=E)) (s • x)‖ * ‖s • ContinuousLinearMap.id ℝ E‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (max R 0)*s := by
      have h1 : ‖fderiv ℝ (radialBase (E:=E)) (s • x)‖≤max R 0 :=
        (hR (Set.mem_range_self _)).trans (le_max_left _ _)
      have h2 : ‖s • ContinuousLinearMap.id ℝ E‖≤s := by
        rw [norm_smul,Real.norm_of_nonneg hs]
        exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
      exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
    _ = _ := by dsimp [s]; ring

theorem radialCutoff_derivative_integrable {μ : Measure E} {T:E→E}
    (hT : Integrable T μ) (n:ℕ) :
    Integrable (fun x => (fderiv ℝ (radialCutoff n) x) (T x)) μ := by
  obtain ⟨C,_,hbound⟩ := radialCutoff_fderiv_bound (E:=E)
  apply (hT.norm.const_mul (C/((n:ℝ)+1))).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((radialCutoff_contDiff (E:=E) n).continuous_fderiv (by simp)).aestronglyMeasurable.prodMk
        hT.aestronglyMeasurable))
  filter_upwards with x
  exact ((fderiv ℝ (radialCutoff n) x).le_opNorm (T x)).trans
    (mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _))

theorem radialCutoff_mul_integrable {μ : Measure E} {f:E→ℝ}
    (hf : Integrable f μ) (n:ℕ) : Integrable (fun x => radialCutoff n x*f x) μ := by
  apply hf.norm.mono' ((radialCutoff_contDiff (E:=E) n).continuous.aestronglyMeasurable.mul
    hf.aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.mul_apply]
  rw [norm_mul,Real.norm_of_nonneg (radialCutoff_mem_Icc n x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_mem_Icc n x).2

theorem radialCutoff_derivative_error {μ : Measure E} {T:E→E} (hT : Integrable T μ) :
    Tendsto (fun n => ∫ x,(fderiv ℝ (radialCutoff n) x) (T x) ∂μ) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := radialCutoff_fderiv_bound (E:=E)
  have hp (n:ℕ) (x:E) : ‖(fderiv ℝ (radialCutoff n) x) (T x)‖≤
      C/((n:ℝ)+1)*‖T x‖ :=
    ((fderiv ℝ (radialCutoff n) x).le_opNorm (T x)).trans
      (mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _))
  have hh := tendsto_integral_of_dominated_convergence (fun x => C*‖T x‖)
    (fun n => (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((radialCutoff_contDiff (E:=E) n).continuous_fderiv (by simp)).aestronglyMeasurable.prodMk
        hT.aestronglyMeasurable)) (hT.norm.const_mul C)
    (fun n => Filter.Eventually.of_forall (fun x => (hp n x).trans (by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact div_le_self hC (by have hn := Nat.cast_nonneg (α:=ℝ) n; linarith))))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have ht : Tendsto (fun n:ℕ => C/((n:ℝ)+1)*‖T x‖) atTop (𝓝 0) := by
        simpa only [mul_zero,zero_mul,div_eq_mul_inv,one_div,one_mul] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul C |>.mul_const ‖T x‖
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => hp n x) ht))
  simpa only [integral_zero] using hh

end PersistencePays
#print axioms PersistencePays.radialCutoff_derivative_error
