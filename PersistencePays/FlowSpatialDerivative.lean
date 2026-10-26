import PersistencePays.LinearVariationalExistence
import Mathlib.Analysis.Calculus.MeanValue

/-! Spatial differentiation of an actual flow via its variational equation.
A quadratic field remainder and Grönwall give a quadratic flow remainder;
no differentiability of the flow is assumed. -/
noncomputable section
namespace PersistencePays
open Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasFDerivAt_of_quadratic_bound {f:E→E} {D:E→L[ℝ]E} {x:E} {C:ℝ}
    (hC:0≤C) (hb:∀y,‖f y-f x-D (y-x)‖≤C*‖y-x‖^2) : HasFDerivAt f D x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ:0<ε/(C+1) := div_pos hε (by linarith)
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hdist : ‖y-x‖<ε/(C+1) := by simpa only [mem_ball,dist_eq_norm] using hy
  have hprod : C*‖y-x‖≤ε := by
    have := (lt_div_iff₀ (by linarith : 0<C+1)).mp hdist
    nlinarith [norm_nonneg (y-x)]
  exact (hb y).trans (by nlinarith [norm_nonneg (y-x)])

theorem gronwallBound_zero_scale (K ε c t:ℝ) :
    gronwallBound 0 K (ε*c) t=gronwallBound 0 K ε t*c := by
  by_cases hK:K=0
  · simp [hK,gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK,zero_mul,zero_add]
    ring

theorem flow_remainder_bound {f:ℝ→E→E} {D:ℝ→E→E→L[ℝ]E}
    {Φ:E→ℝ→E} {J:ℝ→E→L[ℝ]E} {a b:ℝ} {x:E}
    {K M P:ℝ} (hM:0≤M) (hP:0≤P)
    (hΦ:∀y,∀t∈Icc a b,HasDerivWithinAt (Φ y) (f t (Φ y t)) (Icc a b) t)
    (hinit:∀y,Φ y a=y)
    (hJ:∀t∈Icc a b,HasDerivWithinAt J ((D t (Φ x t)).comp (J t)) (Icc a b) t)
    (hJinit:J a=ContinuousLinearMap.id ℝ E)
    (hD:∀t∈Icc a b,‖D t (Φ x t)‖≤K)
    (hrem:∀t∈Icc a b,∀y z,‖f t y-f t z-D t z (y-z)‖≤M*‖y-z‖^2)
    (hlip:∀t∈Icc a b,∀y,‖Φ y t-Φ x t‖≤P*‖y-x‖)
    (y:E) (t:ℝ) (ht:t∈Icc a b) :
    ‖Φ y t-Φ x t-J t (y-x)‖≤gronwallBound 0 K (M*P^2) (t-a)*‖y-x‖^2 := by
  let R : ℝ→E := fun s=>Φ y s-Φ x s-J s (y-x)
  let R' : ℝ→E := fun s=>f s (Φ y s)-f s (Φ x s)-D s (Φ x s) (J s (y-x))
  have hd (s:ℝ) (hs:s∈Icc a b) : HasDerivWithinAt R (R' s) (Icc a b) s := by
    have hj := (ContinuousLinearMap.apply ℝ E (y-x)).hasFDerivAt.comp_hasDerivWithinAt s (hJ s hs)
    exact ((hΦ y s hs).sub (hΦ x s hs)).sub hj
  have hc : ContinuousOn R (Icc a b) := fun s hs=>(hd s hs).continuousWithinAt
  have hdr (s:ℝ) (hs:s∈Ico a b) : HasDerivWithinAt R (R' s) (Ici s) s :=
    (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have h0 : ‖R a‖≤0 := by simp [R,hinit,hJinit]
  have hb (s:ℝ) (hs:s∈Ico a b) : ‖R' s‖≤K*‖R s‖+M*P^2*‖y-x‖^2 := by
    have hs' : s∈Icc a b := ⟨hs.1,hs.2.le⟩
    have heq : R' s=D s (Φ x s) (R s)+
        (f s (Φ y s)-f s (Φ x s)-D s (Φ x s) (Φ y s-Φ x s)) := by
      simp only [R,R',map_sub]
      module
    rw [heq]
    calc
      _ ≤ ‖D s (Φ x s) (R s)‖+
          ‖f s (Φ y s)-f s (Φ x s)-D s (Φ x s) (Φ y s-Φ x s)‖ := norm_add_le _ _
      _ ≤ K*‖R s‖+M*‖Φ y s-Φ x s‖^2 := add_le_add
        (((D s (Φ x s)).le_opNorm (R s)).trans
          (mul_le_mul_of_nonneg_right (hD s hs') (norm_nonneg _)))
        (hrem s hs' _ _)
      _ ≤ K*‖R s‖+M*P^2*‖y-x‖^2 := by
        have hsq : ‖Φ y s-Φ x s‖^2≤(P*‖y-x‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hlip s hs' y) 2
        nlinarith [mul_le_mul_of_nonneg_left hsq hM]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hc hdr h0 hb t ht
  rw [gronwallBound_zero_scale] at hh
  exact hh

theorem flow_spatial_hasFDerivAt {f:ℝ→E→E} {D:ℝ→E→E→L[ℝ]E}
    {Φ:E→ℝ→E} {J:ℝ→E→L[ℝ]E} {a b:ℝ} {x:E}
    {K M P:ℝ} (hM:0≤M) (hP:0≤P)
    (hΦ:∀y,∀t∈Icc a b,HasDerivWithinAt (Φ y) (f t (Φ y t)) (Icc a b) t)
    (hinit:∀y,Φ y a=y)
    (hJ:∀t∈Icc a b,HasDerivWithinAt J ((D t (Φ x t)).comp (J t)) (Icc a b) t)
    (hJinit:J a=ContinuousLinearMap.id ℝ E)
    (hD:∀t∈Icc a b,‖D t (Φ x t)‖≤K)
    (hrem:∀t∈Icc a b,∀y z,‖f t y-f t z-D t z (y-z)‖≤M*‖y-z‖^2)
    (hlip:∀t∈Icc a b,∀y,‖Φ y t-Φ x t‖≤P*‖y-x‖)
    (t:ℝ) (ht:t∈Icc a b) : HasFDerivAt (fun y=>Φ y t) (J t) x := by
  let C:=gronwallBound 0 K (M*P^2) (t-a)
  apply hasFDerivAt_of_quadratic_bound (C:=max C 0) (le_max_right _ _)
  intro y
  exact (flow_remainder_bound hM hP hΦ hinit hJ hJinit hD hrem hlip y t ht).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (sq_nonneg _))

end PersistencePays
#print axioms PersistencePays.flow_spatial_hasFDerivAt
