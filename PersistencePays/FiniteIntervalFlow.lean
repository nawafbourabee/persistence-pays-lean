import PersistencePays.ScaledMeanFlow
import PersistencePays.VariationalFlow

/-! A bijective finite-interval flow obtained from actual trajectories and
uniqueness. All initial times are allowed, including interval endpoints. -/
noncomputable section
namespace PersistencePays
open Set Metric
open scoped NNReal
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem intervalODE_unique {f:ℝ→E→E} {X Y:ℝ→E} {a b τ:ℝ} {K:ℝ≥0}
    (hl:∀t∈Icc a b,LipschitzWith K (f t)) (hτ:τ∈Icc a b)
    (hX:∀t∈Icc a b,HasDerivWithinAt X (f t (X t)) (Icc a b) t)
    (hY:∀t∈Icc a b,HasDerivWithinAt Y (f t (Y t)) (Icc a b) t)
    (hi:X τ=Y τ) : EqOn X Y (Icc a b) := by
  have hXc:ContinuousOn X (Icc a b) := fun t ht=>(hX t ht).continuousWithinAt
  have hYc:ContinuousOn Y (Icc a b) := fun t ht=>(hY t ht).continuousWithinAt
  intro t ht
  by_cases htτ:t≤τ
  · have hsub:Icc a τ⊆Icc a b := Icc_subset_Icc_right hτ.2
    apply ODE_solution_unique_of_mem_Icc_left (s:=fun _=>univ) (K:=K)
      (fun s hs=>(hl s (hsub ⟨hs.1.le,hs.2⟩)).lipschitzOnWith)
      (hXc.mono hsub) (fun s hs=>(hX s (hsub ⟨hs.1.le,hs.2⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1,hs.2.trans hτ.2⟩)) (fun _ _=>mem_univ _)
      (hYc.mono hsub) (fun s hs=>(hY s (hsub ⟨hs.1.le,hs.2⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1,hs.2.trans hτ.2⟩)) (fun _ _=>mem_univ _) hi
    exact ⟨ht.1,htτ⟩
  · have hsub:Icc τ b⊆Icc a b := Icc_subset_Icc_left hτ.1
    apply ODE_solution_unique_of_mem_Icc_right (s:=fun _=>univ) (K:=K)
      (fun s hs=>(hl s (hsub ⟨hs.1,hs.2.le⟩)).lipschitzOnWith)
      (hXc.mono hsub) (fun s hs=>(hX s (hsub ⟨hs.1,hs.2.le⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hτ.1.trans hs.1,hs.2⟩)) (fun _ _=>mem_univ _)
      (hYc.mono hsub) (fun s hs=>(hY s (hsub ⟨hs.1,hs.2.le⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hτ.1.trans hs.1,hs.2⟩)) (fun _ _=>mem_univ _) hi
    exact ⟨(not_le.mp htτ).le,ht.2⟩

theorem finite_interval_flow {f:ℝ→E→E} {a b:ℝ} {K:ℝ≥0} (hab:a≤b)
    (hl:∀t∈Icc a b,LipschitzWith K (f t))
    (hex:∀τ:Icc a b,∀x:E,∃X:ℝ→E,X τ=x ∧
      ∀t∈Icc a b,HasDerivWithinAt X (f t (X t)) (Icc a b) t) :
    ∃Φ:ℝ→E→E,
      (∀x,Φ a x=x) ∧
      (∀t∈Icc a b,∀x,HasDerivWithinAt (fun s=>Φ s x) (f t (Φ t x)) (Icc a b) t) ∧
      (∀t∈Icc a b,Function.Bijective (Φ t)) ∧
      (∀t∈Icc a b,LipschitzWith ⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩ (Φ t)) := by
  choose X hi hd using hex
  let τ₀:Icc a b:=⟨a,le_rfl,hab⟩
  let Φ:ℝ→E→E:=fun t x=>X τ₀ x t
  have hini (x:E):Φ a x=x := hi τ₀ x
  have hder (t:ℝ) (ht:t∈Icc a b) (x:E):
      HasDerivWithinAt (fun s=>Φ s x) (f t (Φ t x)) (Icc a b) t := hd τ₀ x t ht
  refine ⟨Φ,hini,hder,?_,?_⟩
  · intro t ht
    constructor
    · intro x y hxy
      have heq:=intervalODE_unique hl ht (fun s hs=>hder s hs x)
        (fun s hs=>hder s hs y) hxy ⟨le_rfl,hab⟩
      simpa only [hini] using heq
    · intro y
      let τ:Icc a b:=⟨t,ht⟩
      refine ⟨X τ y a,?_⟩
      have heq:=intervalODE_unique hl (show a∈Icc a b from ⟨le_rfl,hab⟩)
        (fun s hs=>hder s hs (X τ y a)) (hd τ y) (hini (X τ y a)) ht
      exact heq.trans (hi τ y)
  · intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc (z:E):ContinuousOn (fun s=>Φ s z) (Icc a b) :=
      fun s hs=>(hder s hs z).continuousWithinAt
    have hr (z:E) (s:ℝ) (hs:s∈Ico a b):
        HasDerivWithinAt (fun u=>Φ u z) (f s (Φ s z)) (Ici s) s :=
      (hder s ⟨hs.1,hs.2.le⟩ z).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    have hg:=dist_le_of_trajectories_ODE_of_mem (s:=fun _=>univ)
      (fun s hs=>(hl s ⟨hs.1,hs.2.le⟩).lipschitzOnWith)
      (hc x) (hr x) (fun _ _=>mem_univ _) (hc y) (hr y) (fun _ _=>mem_univ _)
      (show dist (Φ a x) (Φ a y)≤dist x y by rw [hini,hini]) t ht
    calc
      dist (Φ t x) (Φ t y) ≤ dist x y*Real.exp ((K:ℝ)*(t-a)) := hg
      _ ≤ dist x y*Real.exp ((K:ℝ)*(b-a)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) K.property)) dist_nonneg
      _ = _ := mul_comm _ _

end PersistencePays
#print axioms PersistencePays.finite_interval_flow
