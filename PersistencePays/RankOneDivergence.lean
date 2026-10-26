import PersistencePays.MatrixDivergenceProduct
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Exact stress-divergence algebra for the conditional-mean acceleration.
The identities are analytic product rules, with all differentiation discharged. -/
noncomputable section
namespace PersistencePays
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def vectorDivergence (b : E → E) (x : E) : ℝ :=
  ∑ i, ⟪fderiv ℝ b x (stdOrthonormalBasis ℝ E i),stdOrthonormalBasis ℝ E i⟫_ℝ

def rankOneField (b : E → E) (x : E) : E →L[ℝ] E :=
  (innerSL ℝ (b x)).smulRight (b x)

theorem rankOneField_contDiff {b : E → E} (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (rankOneField b) := by
  exact ((ContinuousLinearMap.smulRightL ℝ E E).contDiff.comp
    ((innerSL ℝ).contDiff.comp hb)).clm_apply hb

theorem rankOneField_column_derivative {b : E → E} (hb : ContDiff ℝ 1 b)
    (x v w : E) :
    (fderiv ℝ (rankOneField b) x w) v =
      ⟪fderiv ℝ b x w,v⟫_ℝ • b x + ⟪b x,v⟫_ℝ • fderiv ℝ b x w := by
  rw [← matrix_column_fderiv (rankOneField_contDiff hb)]
  have hd := ((hb.differentiable one_ne_zero x).hasFDerivAt.inner ℝ
    (hasFDerivAt_const v x)).smul (hb.differentiable one_ne_zero x).hasFDerivAt
  change HasFDerivAt (fun y => ⟪b y,v⟫_ℝ • b y) _ x at hd
  change fderiv ℝ (fun y => ⟪b y,v⟫_ℝ • b y) x w = _
  rw [hd.fderiv]
  simp [add_comm]

theorem matrixDivergence_rankOne {b : E → E} (hb : ContDiff ℝ 1 b) (x : E) :
    matrixDivergence (rankOneField b) x =
      vectorDivergence b x • b x + fderiv ℝ b x (b x) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hs : (∑ i, ⟪b x,e i⟫_ℝ • fderiv ℝ b x (e i)) = fderiv ℝ b x (b x) := by
    conv_rhs => rw [← e.sum_repr (b x),map_sum]
    simp only [map_smul,e.repr_apply_apply,real_inner_comm]
  simp only [matrixDivergence,rankOneField_column_derivative hb,Finset.sum_add_distrib,
    ← Finset.sum_smul]
  exact congrArg (fun v => vectorDivergence b x • b x+v) hs

theorem vectorDivergence_smul {n : E → ℝ} {b : E → E}
    (hn : ContDiff ℝ 1 n) (hb : ContDiff ℝ 1 b) (x : E) :
    vectorDivergence (fun y => n y • b y) x =
      n x*vectorDivergence b x + fderiv ℝ n x (b x) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hd := (hn.differentiable one_ne_zero x).hasFDerivAt.smul
    (hb.differentiable one_ne_zero x).hasFDerivAt
  have hs : (∑ i, ⟪b x,e i⟫_ℝ * fderiv ℝ n x (e i)) = fderiv ℝ n x (b x) := by
    conv_rhs => rw [← e.sum_repr (b x),map_sum]
    simp only [map_smul,e.repr_apply_apply,smul_eq_mul,real_inner_comm]
  change HasFDerivAt (fun y => n y • b y) _ x at hd
  unfold vectorDivergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,inner_add_left,real_inner_smul_left,
    Finset.sum_add_distrib,← Finset.mul_sum]
  change n x*(∑ i,⟪fderiv ℝ b x (e i),e i⟫_ℝ)+
    (∑ i,fderiv ℝ n x (e i)*⟪b x,e i⟫_ℝ) = _
  rw [show (∑ i,fderiv ℝ n x (e i)*⟪b x,e i⟫_ℝ)=fderiv ℝ n x (b x) by
    simpa only [mul_comm] using hs]

theorem matrixDivergence_weighted_rankOne {n : E → ℝ} {b : E → E}
    (hn : ContDiff ℝ 1 n) (hb : ContDiff ℝ 1 b) (x : E) :
    matrixDivergence (fun y => n y • rankOneField b y) x =
      vectorDivergence (fun y => n y • b y) x • b x + n x • fderiv ℝ b x (b x) := by
  rw [matrixDivergence_smul hn (rankOneField_contDiff hb),matrixDivergence_rankOne hb,
    vectorDivergence_smul hn hb]
  simp only [rankOneField,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    inner_gradient_right,RCLike.conj_to_real]
  module

theorem vectorDivergence_eq_trace (b : E → E) (x : E) :
    vectorDivergence b x = (fderiv ℝ b x).toLinearMap.trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  simp only [vectorDivergence,ContinuousLinearMap.coe_coe,real_inner_comm]

theorem matrixDivergence_sub {M S : E → E →L[ℝ] E}
    (hM : ContDiff ℝ 1 M) (hS : ContDiff ℝ 1 S) (x : E) :
    matrixDivergence (fun y => M y-S y) x = matrixDivergence M x-matrixDivergence S x := by
  classical
  have hd := (hM.differentiable one_ne_zero x).hasFDerivAt.sub
    (hS.differentiable one_ne_zero x).hasFDerivAt
  change HasFDerivAt (fun y=>M y-S y) _ x at hd
  simp only [matrixDivergence,hd.fderiv,ContinuousLinearMap.sub_apply,Finset.sum_sub_distrib]

/-- Continuity and momentum conservation yield the precise material-derivative
identity for the conditional mean. The stress is the second moment minus the
rank-one mean part; all spatial and temporal product rules are proved. -/
theorem material_derivative_from_moment_PDE
    {n : ℝ → E → ℝ} {b : ℝ → E → E} {M : E → E →L[ℝ] E}
    {t : ℝ} {x : E} {ndot : ℝ} {bdot : E}
    (hn : ContDiff ℝ 1 (n t)) (hb : ContDiff ℝ 1 (b t)) (hM : ContDiff ℝ 1 M)
    (hnT : HasDerivAt (fun s=>n s x) ndot t)
    (hbT : HasDerivAt (fun s=>b s x) bdot t)
    (hcontinuity : ndot+vectorDivergence (fun y=>n t y • b t y) x=0)
    (hmomentum : deriv (fun s=>n s x • b s x) t+matrixDivergence M x=0) :
    n t x • (bdot+fderiv ℝ (b t) x (b t x)) =
      -matrixDivergence (fun y=>M y-n t y • rankOneField (b t) y) x := by
  have hd := hnT.smul hbT
  change HasDerivAt (fun s=>n s x • b s x) _ t at hd
  rw [hd.deriv] at hmomentum
  have hs : ContDiff ℝ 1 (fun y=>n t y • rankOneField (b t) y) :=
    hn.smul (rankOneField_contDiff hb)
  rw [matrixDivergence_sub hM hs,
    matrixDivergence_weighted_rankOne hn hb]
  have hnD : ndot = -vectorDivergence (fun y=>n t y • b t y) x := by linarith
  rw [hnD] at hmomentum
  have hm : matrixDivergence M x =
      vectorDivergence (fun y=>n t y • b t y) x • b t x-n t x • bdot := by
    calc
      _ = -(n t x • bdot+(-vectorDivergence (fun y=>n t y • b t y) x) • b t x) :=
        eq_neg_of_add_eq_zero_right hmomentum
      _ = _ := by module
  rw [hm]
  module

end PersistencePays
#print axioms PersistencePays.matrixDivergence_weighted_rankOne

#print axioms PersistencePays.material_derivative_from_moment_PDE
