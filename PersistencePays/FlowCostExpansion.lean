import PersistencePays.Corrector
import PersistencePays.FlowTaylor

/-! Quantitative squared-cost expansion with a cubic mean-square trajectory remainder. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_taylor_identity (ξ v a r:E) (θ:ℝ) :
    ‖ξ+θ • v+(θ^2/2) • a+r‖^2/2=
      ‖ξ‖^2/2+θ*⟪v,ξ⟫+(θ^2/2)*(‖v‖^2+⟪a,ξ⟫)+
      ⟪r,ξ⟫+(θ^3/2)*⟪v,a⟫+θ*⟪v,r⟫+
      (θ^4/8)*‖a‖^2+(θ^2/2)*⟪a,r⟫+‖r‖^2/2 := by
  simp only [←real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm ξ v,real_inner_comm ξ a,real_inner_comm ξ r,
    real_inner_comm r v,real_inner_comm r a,real_inner_comm a v]
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} [IsFiniteMeasure μ]

theorem abs_integral_inner_le_moment_bounds {f g:Ω→E}
    (hf:MemLp f 2 μ) (hg:MemLp g 2 μ) {B C:ℝ} (hB:0≤B) (hC:0≤C)
    (hfB:∫x,‖f x‖^2 ∂μ≤B^2) (hgC:∫x,‖g x‖^2 ∂μ≤C^2) :
    |∫x,⟪f x,g x⟫ ∂μ|≤B*C := by
  refine (abs_integral_inner_le_sqrt hf hg).trans ?_
  apply mul_le_mul
  · exact (Real.sqrt_le_left hB).mpr hfB
  · exact (Real.sqrt_le_left hC).mpr hgC
  · positivity
  · exact hB

set_option backward.isDefEq.respectTransparency false in
theorem integral_quadratic_taylor_identity {ξ v a r:Ω→E} (θ:ℝ)
    (hξ:MemLp ξ 2 μ) (hv:MemLp v 2 μ) (ha:MemLp a 2 μ) (hr:MemLp r 2 μ) :
    (∫x,‖ξ x+θ • v x+(θ^2/2) • a x+r x‖^2/2 ∂μ)=
      (∫x,‖ξ x‖^2 ∂μ)/2+θ*(∫x,⟪v x,ξ x⟫ ∂μ)+
      (θ^2/2)*((∫x,‖v x‖^2 ∂μ)+(∫x,⟪a x,ξ x⟫ ∂μ))+
      (∫x,⟪r x,ξ x⟫ ∂μ)+(θ^3/2)*(∫x,⟪v x,a x⟫ ∂μ)+
      θ*(∫x,⟪v x,r x⟫ ∂μ)+(θ^4/8)*(∫x,‖a x‖^2 ∂μ)+
      (θ^2/2)*(∫x,⟪a x,r x⟫ ∂μ)+(∫x,‖r x‖^2 ∂μ)/2 := by
  have hi0 := hξ.integrable_norm_pow'.div_const 2
  have hi1 := (integrable_inner_of_memLp_two hv hξ).const_mul θ
  have hi2 := (hv.integrable_norm_pow'.add
    (integrable_inner_of_memLp_two ha hξ)).const_mul (θ^2/2)
  have hi3 := integrable_inner_of_memLp_two hr hξ
  have hi4 := (integrable_inner_of_memLp_two hv ha).const_mul (θ^3/2)
  have hi5 := (integrable_inner_of_memLp_two hv hr).const_mul θ
  have hi6 := ha.integrable_norm_pow'.const_mul (θ^4/8)
  have hi7 := (integrable_inner_of_memLp_two ha hr).const_mul (θ^2/2)
  have hi8 := hr.integrable_norm_pow'.div_const 2
  have he := integral_congr_ae (μ:=μ) (Filter.Eventually.of_forall
    (fun x=>quadratic_taylor_identity (ξ x) (v x) (a x) (r x) θ))
  have hs1 := integral_add hi0 hi1
  have hs2 := integral_add (hi0.add hi1) hi2
  have hs3 := integral_add ((hi0.add hi1).add hi2) hi3
  have hs4 := integral_add (((hi0.add hi1).add hi2).add hi3) hi4
  have hs5 := integral_add ((((hi0.add hi1).add hi2).add hi3).add hi4) hi5
  have hs6 := integral_add (((((hi0.add hi1).add hi2).add hi3).add hi4).add hi5) hi6
  have hs7 := integral_add ((((((hi0.add hi1).add hi2).add hi3).add hi4).add hi5).add hi6) hi7
  have hs8 := integral_add (((((((hi0.add hi1).add hi2).add hi3).add hi4).add hi5).add hi6).add hi7) hi8
  simp only [Pi.add_apply] at hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
  rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1] at he
  simpa only [integral_const_mul,integral_div,
    integral_add hv.integrable_norm_pow' (integrable_inner_of_memLp_two ha hξ)] using he

private theorem signed_mul_bound {c z C M:ℝ} (hc:|c|≤C) (hz:|z|≤M) : c*z≤C*M := by
  calc
    c*z ≤ |c*z| := le_abs_self _
    _ = |c| * |z| := abs_mul _ _
    _ ≤ C*M := mul_le_mul hc hz (abs_nonneg _) ((abs_nonneg _).trans hc)

private theorem cubic_error_arithmetic {θ K rx va vr aa ar rr:ℝ}
    (hθ:|θ|≤1) (hK:0≤K) (hrx:|rx|≤K*|θ|^3) (hva:|va|≤K)
    (hvr:|vr|≤K*|θ|^3) (haa:0≤aa) (haaK:aa≤K)
    (har:|ar|≤K*|θ|^3) (hrr:rr≤K*|θ|^6) :
    rx+(θ^3/2)*va+θ*vr+(θ^4/8)*aa+(θ^2/2)*ar+rr/2≤6*K*|θ|^3 := by
  have hp4 : |θ|^4≤|θ|^3 := pow_le_pow_of_le_one (abs_nonneg _) hθ (by omega)
  have hp6 : |θ|^6≤|θ|^3 := pow_le_pow_of_le_one (abs_nonneg _) hθ (by omega)
  have hc3 : |θ^3/2|≤|θ|^3 := by rw [abs_div,abs_pow]; norm_num
  have hc4 : |θ^4/8|≤|θ|^3 := by
    rw [abs_div,abs_pow]; norm_num
    linarith [pow_nonneg (abs_nonneg θ) 4]
  have hc2 : |θ^2/2|≤1 := by
    rw [abs_div,abs_pow]; norm_num
    have hh := mul_le_mul hθ hθ (abs_nonneg θ) zero_le_one
    simp only [←pow_two,sq_abs,mul_one] at hh
    linarith
  have h1 := (le_abs_self rx).trans hrx
  have h2 := signed_mul_bound hc3 hva
  have h3 := signed_mul_bound hθ hvr
  have h4 := signed_mul_bound hc4 (show |aa|≤K by rwa [abs_of_nonneg haa])
  have h5 := signed_mul_bound hc2 har
  have h6 : rr/2≤K*|θ|^3 := by
    have hh := mul_le_mul_of_nonneg_left hp6 hK
    nlinarith [mul_nonneg hK (pow_nonneg (abs_nonneg θ) 3)]
  nlinarith

theorem integral_quadratic_taylor_bound {ξ v a r:Ω→E} {θ B:ℝ}
    (hθ:|θ|≤1) (hB:0≤B)
    (hξ:MemLp ξ 2 μ) (hv:MemLp v 2 μ) (ha:MemLp a 2 μ) (hr:MemLp r 2 μ)
    (hξB:∫x,‖ξ x‖^2 ∂μ≤B^2) (hvB:∫x,‖v x‖^2 ∂μ≤B^2)
    (haB:∫x,‖a x‖^2 ∂μ≤B^2) (hrB:∫x,‖r x‖^2 ∂μ≤(B*|θ|^3)^2) :
    (∫x,‖ξ x+θ • v x+(θ^2/2) • a x+r x‖^2/2 ∂μ)≤
      (∫x,‖ξ x‖^2 ∂μ)/2+θ*(∫x,⟪v x,ξ x⟫ ∂μ)+
      (θ^2/2)*((∫x,‖v x‖^2 ∂μ)+(∫x,⟪a x,ξ x⟫ ∂μ))+6*B^2*|θ|^3 := by
  have hBr : 0≤B*|θ|^3 := by positivity
  have h1 := abs_integral_inner_le_moment_bounds hr hξ hBr hB hrB hξB
  have h2 := abs_integral_inner_le_moment_bounds hv ha hB hB hvB haB
  have h3 := abs_integral_inner_le_moment_bounds hv hr hB hBr hvB hrB
  have h4 := abs_integral_inner_le_moment_bounds ha hr hB hBr haB hrB
  have he := cubic_error_arithmetic (K:=B^2) hθ (sq_nonneg B)
    (by convert h1 using 1 <;> ring) (by convert h2 using 1 <;> ring)
    (by convert h3 using 1 <;> ring)
    (integral_nonneg (fun _=>sq_nonneg _)) haB
    (by convert h4 using 1 <;> ring) (by convert hrB using 1 <;> ring)
  rw [integral_quadratic_taylor_identity θ hξ hv ha hr]
  linarith

end PersistencePays
#print axioms PersistencePays.quadratic_taylor_identity
#print axioms PersistencePays.abs_integral_inner_le_moment_bounds

#print axioms PersistencePays.integral_quadratic_taylor_identity

#print axioms PersistencePays.integral_quadratic_taylor_bound
