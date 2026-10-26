import PersistencePays.Assumptions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual potential/gradient/Hessian scaling for the m=1 reduction.
The original sampler need not evaluate its minimizer; this is a proof coordinate change. -/
noncomputable section
namespace PersistencePays
open scoped InnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def scaledPotential (U:E→ℝ) (x₀:E) (c:ℝ) (y:E):ℝ := U (x₀+c•y)-U x₀

def A1.normalizedPotential {U:E→ℝ} {m L:ℝ} (a:A1 U m L) : E→ℝ :=
  scaledPotential U a.minimizer (Real.sqrt m)⁻¹

theorem A1.scaledPotential_contDiff {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x₀:E) (c:ℝ) :
    ContDiff ℝ 2 (scaledPotential U x₀ c) :=
  (a.twice_contDiff.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub contDiff_const

theorem A1.scaledPotential_gradient {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x₀:E) (c:ℝ) (y:E) :
    gradient (scaledPotential U x₀ c) y=c•gradient U (x₀+c•y) := by
  have hgrad:HasGradientAt (scaledPotential U x₀ c) (c•gradient U (x₀+c•y)) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hp:HasFDerivAt (fun z:E=>x₀+c•z) (c•ContinuousLinearMap.id ℝ E) y:=by
      convert! ((hasFDerivAt_id (𝕜:=ℝ) y).const_smul c).const_add x₀ using 1
    have hh:=((a.hasGradientAt (x₀+c•y)).hasFDerivAt.comp y hp).sub_const (U x₀)
    convert! hh using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply,inner_smul_left,inner_smul_right]
  exact hgrad.gradient

theorem A1.scaledPotential_hessian {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x₀:E) (c:ℝ) (y:E) :
    hessian (scaledPotential U x₀ c) y=c^2•hessian U (x₀+c•y) := by
  have heq:gradient (scaledPotential U x₀ c)=fun z=>c•gradient U (x₀+c•z):=by
    funext z
    exact a.scaledPotential_gradient x₀ c z
  have hp:HasFDerivAt (fun z:E=>x₀+c•z) (c•ContinuousLinearMap.id ℝ E) y:=by
    convert! ((hasFDerivAt_id (𝕜:=ℝ) y).const_smul c).const_add x₀ using 1
  have hh:=((a.hasHessianAt (x₀+c•y)).comp y hp).const_smul c
  unfold hessian
  rw [heq]
  convert! hh.fderiv using 1
  ext v
  simp [hessian,ContinuousLinearMap.map_smul,smul_smul,pow_two]

theorem A1.scaledPotential_A1 {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x₀:E)
    {c:ℝ} (hc:0<c) : A1 (scaledPotential U x₀ c) (c^2*m) (c^2*L) := by
  refine ⟨a.scaledPotential_contDiff x₀ c,mul_pos (sq_pos_of_pos hc) a.m_pos,
    mul_le_mul_of_nonneg_left a.m_le_L (sq_nonneg c),?_,?_⟩
  · intro y v
    rw [a.scaledPotential_hessian]
    simp only [ContinuousLinearMap.smul_apply,inner_smul_left,conj_trivial]
    nlinarith [mul_le_mul_of_nonneg_left (a.lower (x₀+c•y) v) (sq_nonneg c)]
  · intro y v
    rw [a.scaledPotential_hessian]
    simp only [ContinuousLinearMap.smul_apply,inner_smul_left,conj_trivial]
    nlinarith [mul_le_mul_of_nonneg_left (a.upper (x₀+c•y) v) (sq_nonneg c)]

theorem A1.scaledPotential_A2 {U:E→ℝ} {m L LH:ℝ} (a:A1 U m L) (a2:A2 U LH)
    (x₀:E) {c:ℝ} (hc:0<c) : A2 (scaledPotential U x₀ c) (c^3*LH) := by
  constructor
  intro x y
  rw [a.scaledPotential_hessian,a.scaledPotential_hessian,← smul_sub,norm_smul,
    Real.norm_of_nonneg (sq_nonneg c)]
  have hn:‖(x₀+c•x)-(x₀+c•y)‖=c*‖x-y‖:=by
    rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg hc.le]
  have hh:=mul_le_mul_of_nonneg_left (a2.lipschitz (x₀+c•x) (x₀+c•y)) (sq_nonneg c)
  rw [hn] at hh
  nlinarith

theorem A1.normalizedPotential_A1 {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    A1 a.normalizedPotential 1 (L/m) := by
  have hs:0<Real.sqrt m:=Real.sqrt_pos.mpr a.m_pos
  have hh:=a.scaledPotential_A1 a.minimizer (inv_pos.mpr hs)
  have h1:(Real.sqrt m)⁻¹^2*m=1:=by
    rw [inv_pow,Real.sq_sqrt a.m_pos.le]
    exact inv_mul_cancel₀ a.m_pos.ne'
  have hL:(Real.sqrt m)⁻¹^2*L=L/m:=by
    rw [inv_pow,Real.sq_sqrt a.m_pos.le]
    ring
  simpa only [h1,hL,A1.normalizedPotential] using hh

theorem A1.normalizedPotential_A2 {U:E→ℝ} {m L LH:ℝ} (a:A1 U m L) (a2:A2 U LH) :
    A2 a.normalizedPotential (LH/m^(3/2:ℝ)) := by
  have hs:0<Real.sqrt m:=Real.sqrt_pos.mpr a.m_pos
  have hh:=a.scaledPotential_A2 a2 a.minimizer (inv_pos.mpr hs)
  have hs3:(Real.sqrt m)^3=m^(3/2:ℝ):=by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast a.m_pos.le]
    norm_num
  have hc:(Real.sqrt m)⁻¹^3*LH=LH/m^(3/2:ℝ):=by
    rw [inv_pow,hs3]
    ring
  simpa only [hc,A1.normalizedPotential] using hh

theorem A1.normalizedPotential_gradient {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x:E) :
    gradient a.normalizedPotential x=(Real.sqrt m)⁻¹•
      gradient U (a.minimizer+(Real.sqrt m)⁻¹•x) :=
  a.scaledPotential_gradient a.minimizer (Real.sqrt m)⁻¹ x

theorem A1.normalizedPotential_zero {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    a.normalizedPotential 0=0 := by simp [A1.normalizedPotential,scaledPotential]

theorem A1.normalizedPotential_nonnegative {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (y:E) :
    0≤a.normalizedPotential y := sub_nonneg.mpr (a.minimizer_le _)

theorem A1.normalizedPotential_minimizer {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    a.normalizedPotential_A1.minimizer=0 := by
  symm
  apply a.normalizedPotential_A1.minimizer_unique
  intro y
  rw [a.normalizedPotential_zero]
  exact a.normalizedPotential_nonnegative y
end PersistencePays
#print axioms PersistencePays.A1.normalizedPotential_A1
#print axioms PersistencePays.A1.scaledPotential_A2

#print axioms PersistencePays.A1.normalizedPotential_A2
