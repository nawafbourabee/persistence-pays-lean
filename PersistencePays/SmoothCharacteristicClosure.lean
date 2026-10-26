import PersistencePays.MeanFlowLocalTaylor

/-! Closing the corrector argument from actual smooth characteristic flows,
density evolution, and the signed static acceleration inequality. All local
couplings, uniform moments, and Taylor remainders are constructed here. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance smoothClosureProdNorm : NormedAddCommGroup (ℝ×E) := inferInstance
local instance smoothClosureProdSpace : NormedSpace ℝ (ℝ×E) := inferInstance
local instance smoothClosureOperatorNorm : NormedAddCommGroup ((ℝ×E)→L[ℝ]E) := inferInstance

private lemma common_square_bound (b v a j:ℝ) (hb:0≤b) :
    ∃B:ℝ,0≤B ∧ b^2≤B^2 ∧ v≤B^2 ∧ a≤B^2 ∧ j≤B^2 := by
  let B:=1+|b|+|v|+|a|+|j|
  have hbB:b≤B:=by dsimp [B]; linarith [le_abs_self b,abs_nonneg v,abs_nonneg a,abs_nonneg j]
  have h1:1≤B:=by dsimp [B]; linarith [abs_nonneg b,abs_nonneg v,abs_nonneg a,abs_nonneg j]
  have hv:v≤B:=by dsimp [B]; linarith [le_abs_self v,abs_nonneg b,abs_nonneg a,abs_nonneg j]
  have ha:a≤B:=by dsimp [B]; linarith [le_abs_self a,abs_nonneg b,abs_nonneg v,abs_nonneg j]
  have hj:j≤B:=by dsimp [B]; linarith [le_abs_self j,abs_nonneg b,abs_nonneg v,abs_nonneg a]
  have hB:0≤B:=by linarith
  have hBB:B≤B^2:=by nlinarith
  exact ⟨B,hB,(sq_le_sq₀ hb hB).mpr hbB,hv.trans hBB,ha.trans hBB,hj.trans hBB⟩

theorem A1.free_transport_of_smooth_characteristics {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ8:MemLp id 8 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (hac:μ≪(volume:Measure E).prod volume)
    {T δ0 C:ℝ} (hT:0<T) (hδ0:0<δ0) (hC:1≤C)
    (F:ℝ×E→E) (hF:ContDiff ℝ 2 F) (n:ℝ×E→ℝ)
    (hDensity:∀s∈Icc 0 T,transportPosition μ s=
      volume.withDensity (fun x=>ENNReal.ofReal (n (s,x))))
    (hn:∀s∈Icc 0 T,∀x,DifferentiableAt ℝ n (s,x))
    (hpos:∀s∈Icc 0 T,∀x,0<n (s,x))
    (hpde:∀s∈Icc 0 T,∀x,fderiv ℝ n (s,x) (1,F (s,x))=
      -n (s,x)*LinearMap.trace ℝ E (fderiv ℝ (fun y=>F (s,y)) x).toLinearMap)
    (hGrowth:∀s∈Icc 0 T,∀x,
      ‖F (s,x)‖≤C*(1+‖x‖) ∧
      ‖fderiv ℝ F (s,x)‖≤C*(1+‖x‖) ∧
      ‖fderiv ℝ (fderiv ℝ F) (s,x)‖≤C*(1+‖x‖)^2)
    (hmean:∀s∈Icc 0 T,∀ᵐ x∂transportPosition μ s,
      F (s,x)=conditionalMeanVelocity (transportJoint μ s) x)
    (hrate:∀s∈Icc 0 T,
      (∫x,‖F (s,x)‖^2 ∂transportPosition μ s)+
      (∫x,⟪materialAcceleration F (s,x),x-positionBrenierMap
        (transportJoint μ s) a.targetProbability x⟫ ∂transportPosition μ s)≤
      6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U)))
    (hflows:∀s∈Icc 0 T,∀t∈Icc 0 T,|t-s|≤δ0→
      Nonempty (VariationalFlow E (fun u x=>F (u,x))
        (fun u x=>fderiv ℝ (fun y=>F (u,y)) x) (min s t) (max s t))) :
    a.corrector (transportJoint μ T)-a.corrector μ≤freeTransportRHS μ (positionGibbs U) T := by
  have hμ2:MemLp id 2 μ:=hμ8.mono_exponent (by norm_num)
  have hμ4:MemLp id 4 μ:=hμ8.mono_exponent (by norm_num)
  have hC0:0≤C:=by linarith
  have hsabs {s:ℝ} (hs:s∈Icc 0 T):|s|≤|T|:=by
    rw [abs_of_nonneg hs.1,abs_of_pos hT]
    exact hs.2
  let M2:=∫z,freeMomentEnvelope T 2 z ∂μ
  let M4:=∫z,freeMomentEnvelope T 4 z ∂μ
  let M8:=∫z,freeMomentEnvelope T 8 z ∂μ
  have hv (s:ℝ) (hs:s∈Icc 0 T):
      MemLp (fun x=>F (s,x)) 2 (transportPosition μ s) ∧
      (∫x,‖F (s,x)‖^2 ∂transportPosition μ s)≤C^2*M2:=by
    simpa only [pow_one] using freePosition_polynomial_L2 μ 1 hμ2 T s C hC0
      (hsabs hs) (fun x=>F (s,x)) (hF.continuous.measurable.comp (by fun_prop))
      (fun x=>by simpa only [pow_one] using (hGrowth s hs x).1)
  have ha (s:ℝ) (hs:s∈Icc 0 T):
      MemLp (fun x=>materialAcceleration F (s,x)) 2 (transportPosition μ s) ∧
      (∫x,‖materialAcceleration F (s,x)‖^2 ∂transportPosition μ s)≤(C^2)^2*M4:=by
    apply freePosition_polynomial_L2 μ 2 hμ4 T s (C^2) (sq_nonneg C) (hsabs hs) _
      ((materialAcceleration_contDiff hF).continuous.measurable.comp (by fun_prop))
    intro x
    have hh:=hGrowth s hs x
    exact (material_growth hC (s,x) hh.1 hh.2.1 hh.2.2).1
  obtain ⟨bc,hbc,hcost⟩:=freePosition_cost_uniform μ hμ2 a.targetProbability a.position_memLp_two T
  obtain ⟨B,hB,hbcB,hvB,haB,hjB⟩:=common_square_bound bc (C^2*M2) ((C^2)^2*M4) ((32*C^3)^2*M8) hbc
  let δ:=min δ0 (1/(2*C))
  have hδ:0<δ:=lt_min hδ0 (by positivity)
  apply a.free_transport_of_local_mean_maps μ hμ2 hK hac hT hδ hB
    (fun s x=>F (s,x)) (fun s x=>materialAcceleration F (s,x))
    (fun s hs=>(hv s hs).1) (fun s hs=>(ha s hs).1) hmean
    (fun s hs=>(hcost s (hsabs hs)).trans hbcB)
    (fun s hs=>(hv s hs).2.trans hvB) (fun s hs=>(ha s hs).2.trans haB) hrate
  intro s hs t ht hst
  obtain ⟨flow⟩:=hflows s hs t ht (hst.trans (min_le_left _ _))
  have hsub {u:ℝ} (hu:u∈Icc (min s t) (max s t)):u∈Icc 0 T:=
    ⟨(le_min hs.1 ht.1).trans hu.1,hu.2.trans (max_le hs.2 ht.2)⟩
  obtain ⟨X,hX0,hXm,hXd,hmap⟩:=flow.relative_density_trajectory volume min_le_max n
    (fun u hu=>hn u (hsub hu)) (fun u hu=>hpos u (hsub hu))
    (fun u hu=>hpde u (hsub hu))
    ⟨min_le_left s t,le_max_left s t⟩ ⟨min_le_right s t,le_max_right s t⟩
  have hsmall:C*|t-s|≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_left (hst.trans (min_le_right _ _)) hC0
    have he:C*(1/(2*C))=1/2:=by field_simp <;> ring
    exact hh.trans_eq he
  have hJ:(32*C^3)^2*(∫x,(1+‖x‖)^8 ∂transportPosition μ s)≤B^2:=
    (mul_le_mul_of_nonneg_left (freePosition_polynomial_moment μ 8 hμ8 T s (hsabs hs))
      (sq_nonneg _)).trans hjB
  obtain ⟨r,hr,hexp,hrB⟩:=signed_meanFlow_taylor hF (transportPosition μ s)
    (transportPosition_memLp μ hμ8 s) hC hsmall
    (fun u hu=>hGrowth (s+u) (add_mem_interval_of_relative hs ht hu))
    X hX0 (hXm (t-s) right_mem_uIcc) hXd hJ
  refine ⟨X (t-s),r,hXm (t-s) right_mem_uIcc,?_,hr,hexp,hrB⟩
  rw [hDensity s hs,hDensity t ht]
  exact hmap

end PersistencePays
#print axioms PersistencePays.A1.free_transport_of_smooth_characteristics
