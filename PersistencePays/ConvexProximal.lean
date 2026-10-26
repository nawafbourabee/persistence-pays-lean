import PersistencePays.ConvexDifferentiability
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! The actual proximal map of a finite convex function. The minimizer is
constructed by coercivity, its subgradient characterization is proved, and the
resulting map is firmly nonexpansive. These are foundations for second-order
convex regularity, not an assumption of Alexandrov's theorem. -/
open Set Filter
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def Supports (f : E → ℝ) (x v : E) : Prop :=
  ∀ y, f x + ⟪v,y-x⟫ ≤ f y

def proximalObjective (f : E → ℝ) (z x : E) : ℝ := f x + ‖x-z‖^2 / 2

lemma supports_monotone {f : E → ℝ} {x y v w : E}
    (hx : Supports f x v) (hy : Supports f y w) :
    0 ≤ ⟪v-w,x-y⟫ := by
  have h1 := hx y
  have h2 := hy x
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

lemma supports_proximal_minimum {f : E → ℝ} {x z : E}
    (h : Supports f x (z-x)) (y : E) :
    proximalObjective f z x + ‖y-x‖^2 / 2 ≤ proximalObjective f z y := by
  have hs := h y
  have hn : ‖y-z‖^2 = ‖y-x‖^2 + 2*⟪y-x,x-z⟫ + ‖x-z‖^2 := by
    convert norm_add_sq_real (y-x) (x-z) using 1 <;> congr 1 <;> abel
  have hi : ⟪z-x,y-x⟫ = -⟪y-x,x-z⟫ := by
    rw [real_inner_comm]
    simp only [inner_sub_right]
    ring
  dsimp [proximalObjective]
  rw [hi] at hs
  linarith

lemma exists_proximal_minimum {f : E → ℝ} (hf : ConvexOn ℝ univ f) (z : E) :
    ∃ x, ∀ y, proximalObjective f z x ≤ proximalObjective f z y := by
  have hfc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  obtain ⟨l,c,hl,_⟩ := ConvexOn.exists_affine_le_of_lt (𝕜:=ℝ) (x:=(0:E)) (a:=f 0-1)
    (mem_univ _) (by linarith) isClosed_univ (hfc.lowerSemicontinuous.lowerSemicontinuousOn univ) hf
  have hlower (x : E) : c - ‖l‖*‖x‖ ≤ f x := by
    have h1 := hl ⟨x,mem_univ _⟩
    have h2 := l.le_opNorm x
    have h3 := neg_le_abs (l x)
    simp only [domRestrict_apply, Pi.add_apply, Function.const_apply, Function.comp_apply,
      RCLike.re_to_real] at h1
    rw [Real.norm_eq_abs] at h2
    linarith
  have hcoerce (x : E) :
      ‖x‖ + c - (‖l‖+‖z‖+1)^2 / 2 ≤ proximalObjective f z x := by
    have hx := hlower x
    have hi := real_inner_le_norm x z
    have hq := sq_nonneg (‖x‖-(‖l‖+‖z‖+1))
    dsimp [proximalObjective]
    rw [norm_sub_sq_real]
    nlinarith [sq_nonneg ‖z‖]
  have hlim : Tendsto (proximalObjective f z) (cocompact E) atTop := by
    apply tendsto_atTop_mono hcoerce
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
      (tendsto_norm_cocompact_atTop (E:=E)))
  have hc : Continuous (proximalObjective f z) := by
    unfold proximalObjective
    fun_prop
  exact hc.exists_forall_le hlim

lemma minimum_supports {f : E → ℝ} (hf : ConvexOn ℝ univ f) {z x : E}
    (hx : ∀ y, proximalObjective f z x ≤ proximalObjective f z y) :
    Supports f x (z-x) := by
  intro y
  let C := f y-f x+⟪x-z,y-x⟫
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ C+t*‖y-x‖^2/2 := by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num)))] with t ht ht1
    change 0<t at ht
    change t<1 at ht1
    have hc := hf.2 (mem_univ x) (mem_univ y) (show 0≤1-t by linarith)
      ht.le (by ring : (1-t)+t=1)
    have he : (1-t) • x + t • y = x+t•(y-x) := by module
    rw [he] at hc
    simp only [smul_eq_mul] at hc
    have hm := hx (x+t•(y-x))
    have he2 : x+t•(y-x)-z = (x-z)+t•(y-x) := by abel
    dsimp [proximalObjective] at hm
    rw [he2,norm_add_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs] at hm
    have hh : 0 ≤ t*(C+t*‖y-x‖^2/2) := by dsimp [C]; nlinarith
    exact nonneg_of_mul_nonneg_right hh ht
  have hlim : Tendsto (fun t : ℝ => C+t*‖y-x‖^2/2) (𝓝[>] 0) (𝓝 C) := by
    have hc : Continuous (fun t : ℝ => C+t*‖y-x‖^2/2) := by fun_prop
    simpa using hc.continuousWithinAt.tendsto (s:=Ioi 0) (x:=0)
  have hh := ge_of_tendsto hlim hsmall
  dsimp [C] at hh
  have hi : ⟪z-x,y-x⟫ = -⟪x-z,y-x⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hi]
  linarith

theorem existsUnique_proximal {f : E → ℝ} (hf : ConvexOn ℝ univ f) (z : E) :
    ∃! x, Supports f x (z-x) := by
  obtain ⟨x,hx⟩ := exists_proximal_minimum hf z
  refine ⟨x,minimum_supports hf hx,?_⟩
  intro y hy
  have h1 := supports_proximal_minimum hy x
  have h2 := hx y
  have hh : ‖x-y‖^2 ≤ 0 := by linarith
  have he : x-y=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x-y)])
  exact (sub_eq_zero.mp he).symm

def proximalMap (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) : E :=
  (existsUnique_proximal hf z).exists.choose

theorem proximalMap_supports (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) :
    Supports f (proximalMap f hf z) (z-proximalMap f hf z) :=
  (existsUnique_proximal hf z).exists.choose_spec

theorem proximalMap_eq_iff (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z x : E) :
    proximalMap f hf z=x ↔ Supports f x (z-x) := by
  constructor
  · intro h
    simpa [h] using proximalMap_supports f hf z
  · intro h
    exact ((existsUnique_proximal hf z).unique (proximalMap_supports f hf z) h)

theorem proximalMap_firm (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z w : E) :
    ‖proximalMap f hf z-proximalMap f hf w‖^2 ≤
      ⟪z-w,proximalMap f hf z-proximalMap f hf w⟫ := by
  have hh := supports_monotone (proximalMap_supports f hf z) (proximalMap_supports f hf w)
  have he : (z-proximalMap f hf z)-(w-proximalMap f hf w) =
      (z-w)-(proximalMap f hf z-proximalMap f hf w) := by abel
  rw [he,inner_sub_left,real_inner_self_eq_norm_sq] at hh
  linarith

theorem proximalMap_lipschitz (f : E → ℝ) (hf : ConvexOn ℝ univ f) :
    LipschitzWith 1 (proximalMap f hf) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h1 := proximalMap_firm f hf z w
  have h2 := real_inner_le_norm (z-w) (proximalMap f hf z-proximalMap f hf w)
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  nlinarith [norm_nonneg (proximalMap f hf z-proximalMap f hf w), norm_nonneg (z-w)]

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.existsUnique_proximal
#print axioms PersistencePays.QuadraticTransport.proximalMap_lipschitz
