import PersistencePays.GibbsTail
import PersistencePays.LyapunovBounds
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The target position second moment from strong-convex radial scaling.
This derives the bound directly, without assuming an integration-by-parts formula. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.normalized_radial_gradient {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (x : E) :
    ‖x‖^2 ≤ ⟪gradient U x,x⟫ := by
  have h1 := a.normalized_gradient_coercivity hzero x
  have h2 := a.normalized_position_bound hstar hzero x
  rw [real_inner_comm] at h1
  linarith

theorem A1.normalized_radial_potential {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (x : E) (c : ℝ)
    (hc : 0<c) (hc1 : c≤1) :
    U (c•x)+(1-c^2)/2*‖x‖^2 ≤ U x := by
  have hg := a.normalized_radial_gradient hstar hzero (c•x)
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at hg
  have hi : c*‖x‖^2 ≤ ⟪gradient U (c•x),x⟫ := by
    apply le_of_mul_le_mul_left (a := c) _ hc
    nlinarith
  have hs := a.strong_lower_bound (c•x) x
  rw [show x-c•x=(1-c)•x by module, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hi (show 0≤1-c by linarith)
  nlinarith

theorem A1.position_norm_square_integrable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) :
    Integrable (fun x : E => ‖x‖^2) (positionGibbs U) := by
  have hi := a.position_energy_exp_integrable.const_mul 4
  apply hi.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hn := a.normalized_position_bound hstar hzero x
  have he := Real.add_one_le_exp (U x/2)
  simp only [hstar,hzero,sub_zero] at hi ⊢
  linarith

theorem A1.position_memLp_two {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    MemLp id 2 (positionGibbs U) := by
  have hm := a.m_pos
  have hi := a.position_energy_exp_integrable.const_mul (4/m)
  have hcent : Integrable (fun x : E => ‖x-a.minimizer‖^2) (positionGibbs U) := by
    apply hi.mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hp := a.quadratic_lower_at_minimizer x
    have he := Real.add_one_le_exp ((U x-U a.minimizer)/2)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    nlinarith
  have hM : MemLp (fun x : E => x-a.minimizer) 2 (positionGibbs U) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr hcent
  convert hM.add (memLp_const a.minimizer) using 1
  funext x
  simp

theorem A1.position_norm_square_integrable_general {U : E → ℝ} {m L : ℝ} (a : A1 U m L) :
    Integrable (fun x : E => ‖x‖^2) (positionGibbs U) :=
  a.position_memLp_two.integrable_norm_pow'

theorem A1.position_radial_exp_integrable {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (c : ℝ) (hc : 0<c) (hc1 : c≤1) :
    Integrable (fun x : E => Real.exp ((1-c^2)/2*‖x‖^2)) (positionGibbs U) := by
  apply (integrable_tilted_iff a.gibbs_integrable _).mpr
  have hi := a.gibbs_integrable.comp_smul hc.ne'
  apply hi.mono' (by have hU := a.twice_contDiff.continuous; fun_prop)
  filter_upwards with x
  simp only [Real.norm_eq_abs, smul_eq_mul]
  rw [abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := a.normalized_radial_potential hstar hzero x c hc hc1
  linarith

theorem A1.position_radial_mgf {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) (c : ℝ) (hc : 0<c) (hc1 : c≤1) :
    (∫ x : E, Real.exp ((1-c^2)/2*‖x‖^2) ∂positionGibbs U) ≤
      (c^Module.finrank ℝ E)⁻¹ := by
  unfold positionGibbs
  rw [integral_exp_tilted]
  apply (div_le_iff₀ a.gibbs_normalizer_pos).mpr
  have hI : Integrable (fun x : E => Real.exp (-U x+(1-c^2)/2*‖x‖^2)) volume := by
    have hi := (integrable_tilted_iff a.gibbs_integrable _).mp
      (a.position_radial_exp_integrable hstar hzero c hc hc1)
    simpa only [smul_eq_mul, ← Real.exp_add] using hi
  have hupper := a.gibbs_integrable.comp_smul hc.ne'
  have hb : (∫ x : E, Real.exp (-U x+(1-c^2)/2*‖x‖^2)) ≤
      ∫ x : E, Real.exp (-U (c•x)) := by
    apply integral_mono hI hupper
    intro x
    apply Real.exp_le_exp.mpr
    linarith [a.normalized_radial_potential hstar hzero x c hc hc1]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x : E => Real.exp (-U x)) c (hR := hc.le)] at hb
  simpa only [Pi.add_apply,Pi.neg_apply,smul_eq_mul] using hb

theorem derivative_nonnegative_right {f : ℝ → ℝ} {v : ℝ}
    (hf : HasDerivAt f v 0) (hzero : f 0=0) (hpos : ∀ t∈Ioo (0:ℝ) 1, 0≤f t) : 0≤v := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  have hu : Iio (1:ℝ) ∈ 𝓝[>] (0:ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hu] with t ht0 ht1
  have ht : 0<t := ht0
  simpa only [zero_add,hzero,sub_zero,smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr ht.le) (hpos t ⟨ht,ht1⟩)

theorem A1.position_norm_square_le_dim {U : E → ℝ} {L : ℝ} (a : A1 U 1 L)
    (hstar : a.minimizer=0) (hzero : U 0=0) :
    (∫ x : E, ‖x‖^2 ∂positionGibbs U) ≤ (Module.finrank ℝ E : ℝ) := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  let M : ℝ := ∫ x : E, ‖x‖^2 ∂positionGibbs U
  let d := Module.finrank ℝ E
  let f : ℝ → ℝ := fun t => ((1-t)^d)⁻¹-1-(t-t^2/2)*M
  have hd : HasDerivAt (fun t : ℝ => ((1-t)^d)⁻¹) (d:ℝ) 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).const_sub 1).pow d).inv (by simp) using 1 <;> simp
  have hp : HasDerivAt (fun t : ℝ => t-t^2/2) 1 0 := by
    convert! (hasDerivAt_id (0:ℝ)).sub (((hasDerivAt_id (0:ℝ)).pow 2).div_const 2) using 1 <;> norm_num
  have hf : HasDerivAt f ((d:ℝ)-M) 0 := by
    convert! (hd.sub_const 1).sub (hp.mul_const M) using 1 <;> simp [f]
  have hnonneg : 0≤(d:ℝ)-M := by
    apply derivative_nonnegative_right hf (by dsimp [f]; simp)
    intro t ht
    have he := a.position_radial_mgf hstar hzero (1-t) (by linarith [ht.2]) (by linarith [ht.1])
    have hi := a.position_radial_exp_integrable hstar hzero (1-t)
      (by linarith [ht.2]) (by linarith [ht.1])
    have hb : (∫ x : E, ((1-(1-t)^2)/2)*‖x‖^2+1 ∂positionGibbs U) ≤
        ∫ x : E, Real.exp (((1-(1-t)^2)/2)*‖x‖^2) ∂positionGibbs U := by
      apply integral_mono ((a.position_norm_square_integrable hstar hzero).const_mul _ |>.add (integrable_const 1)) hi
      intro x
      exact Real.add_one_le_exp _
    rw [integral_add ((a.position_norm_square_integrable hstar hzero).const_mul _) (integrable_const 1),
      integral_const_mul, integral_const, probReal_univ, one_smul] at hb
    dsimp [f]
    change ((1-t)^d)⁻¹-1-(t-t^2/2)*M ≥ 0
    change ((1-(1-t)^2)/2)*M+1 ≤ _ at hb
    change _ ≤ ((1-t)^d)⁻¹ at he
    nlinarith
  dsimp only [M,d] at hnonneg
  linarith

end PersistencePays
#print axioms PersistencePays.A1.position_norm_square_le_dim
