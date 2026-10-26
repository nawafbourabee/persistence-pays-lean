import PersistencePays.FiniteIntervalFlow
import PersistencePays.FlowSpatialDerivative

/-! Constructing the classical variational flow on a uniform short interval
from actual ODE existence, a bounded derivative, and a quadratic remainder. -/
noncomputable section
namespace PersistencePays
open Set
open scoped NNReal
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem variational_flow_exists {f:ℝ→E→E} {D:ℝ→E→E→L[ℝ]E}
    {a b:ℝ} {K:ℝ≥0} {M:ℝ} (hab:a≤b) (hM:0≤M)
    (hl:∀t∈Icc a b,LipschitzWith K (f t))
    (hDc:Continuous D.uncurry)
    (hDd:∀t∈Icc a b,∀x,HasFDerivAt (f t) (D t x) x)
    (hDb:∀t∈Icc a b,∀x,‖D t x‖≤K)
    (hrem:∀t∈Icc a b,∀y z,‖f t y-f t z-D t z (y-z)‖≤M*‖y-z‖^2)
    (hex:∀τ:Icc a b,∀x:E,∃X:ℝ→E,X τ=x ∧
      ∀t∈Icc a b,HasDerivWithinAt X (f t (X t)) (Icc a b) t)
    (ht:(2*(K:ℝ))*(b-a)≤1) : Nonempty (VariationalFlow E f D a b) := by
  obtain ⟨Φ,hinit,hΦ,hbij,hΦlip⟩:=finite_interval_flow hab hl hex
  let τ:Icc a b:=⟨a,le_rfl,hab⟩
  have hJex (x:E):∃J:ℝ→E→L[ℝ]E,J a=ContinuousLinearMap.id ℝ E ∧
      ∀t∈Icc a b,HasDerivWithinAt J ((D t (Φ t x)).comp (J t)) (Icc a b) t := by
    apply linear_variational_trajectory τ K
    · exact hDc.continuousOn.comp (continuousOn_id.prodMk
        (fun t ht=>(hΦ t ht x).continuousWithinAt)) (fun _ _=>mem_univ _)
    · intro t ht
      exact hDb t ht (Φ t x)
    · simpa [τ,max_eq_left (sub_nonneg.mpr hab)] using ht
  choose J hJi hJd using hJex
  refine ⟨{
    toFun:=Φ
    jacobian:=fun t x=>J x t
    initial:=hinit
    jacobian_initial:=hJi
    field_derivative:=hDd
    time_derivative:=hΦ
    variational_equation:=fun t ht x=>hJd x t ht
    spatial_derivative:=?_
    bijective:=hbij }⟩
  intro t ht x
  apply flow_spatial_hasFDerivAt (Φ:=fun x t=>Φ t x) hM
    (Real.exp_pos ((K:ℝ)*(b-a))).le
    (fun y s hs=>hΦ s hs y) hinit (hJd x) (hJi x)
    (fun s hs=>hDb s hs (Φ s x)) hrem
  · intro s hs y
    have hh := (hΦlip s hs).dist_le_mul y x
    simp only [dist_eq_norm] at hh
    convert hh using 1
    rfl
  · exact ht

end PersistencePays
#print axioms PersistencePays.variational_flow_exists
