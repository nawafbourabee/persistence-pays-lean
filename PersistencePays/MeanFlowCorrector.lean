import PersistencePays.FlowTransportCost
import PersistencePays.MeanAccelerationDefect
import PersistencePays.FreeTransportEntropyContinuity
import PersistencePays.LocalSemiconcavity

/-! Assembly of the local mean-flow couplings into the actual free-transport
corrector inequality. The remaining inputs are explicit endpoint maps and
moment/PDE estimates, supplied by the smooth Gaussian-mixture construction. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def freePositionProbability (μ:Measure (E×E)) [IsProbabilityMeasure μ] (s:ℝ) :
    ProbabilityMeasure E := ⟨transportPosition μ s,inferInstance⟩

theorem A1.free_transport_of_local_mean_maps {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:Measure (E×E)) [IsProbabilityMeasure μ] (hμ:MemLp id 2 μ)
    (hK:klDiv μ (phaseGibbs U)≠∞) (hac:μ≪(volume:Measure E).prod volume)
    {T δ B:ℝ} (hT:0<T) (hδ:0<δ) (hB:0≤B) (v acc:ℝ→E→E)
    (hv:∀s∈Icc 0 T,MemLp (v s) 2 (transportPosition μ s))
    (ha:∀s∈Icc 0 T,MemLp (acc s) 2 (transportPosition μ s))
    (hmean:∀s∈Icc 0 T,∀ᵐ x ∂transportPosition μ s,
      v s x=conditionalMeanVelocity (transportJoint μ s) x)
    (hcost:∀s∈Icc 0 T,
      (QuadraticTransport.cost (freePositionProbability μ s) a.targetProbability).toReal≤B^2)
    (hvB:∀s∈Icc 0 T,∫x,‖v s x‖^2 ∂transportPosition μ s≤B^2)
    (haB:∀s∈Icc 0 T,∫x,‖acc s x‖^2 ∂transportPosition μ s≤B^2)
    (hrate:∀s∈Icc 0 T,
      (∫x,‖v s x‖^2 ∂transportPosition μ s)+
      (∫x,⟪acc s x,x-positionBrenierMap (transportJoint μ s) a.targetProbability x⟫
        ∂transportPosition μ s)≤
      6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
      (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U)))
    (hlocal:∀s∈Icc 0 T,∀t∈Icc 0 T,|t-s|≤δ→
      ∃F r:E→E,Measurable F ∧
      (transportPosition μ s).map F=transportPosition μ t ∧
      MemLp r 2 (transportPosition μ s) ∧
      (∀x,F x=x+(t-s) • v s x+((t-s)^2/2) • acc s x+r x) ∧
      (∫x,‖r x‖^2 ∂transportPosition μ s)≤(B*|t-s|^3)^2) :
    a.corrector (transportJoint μ T)-a.corrector μ≤
      freeTransportRHS μ (positionGibbs U) T := by
  let W : ℝ→ℝ := fun s=>(QuadraticTransport.cost
    (freePositionProbability μ s) a.targetProbability).toReal/2
  let C : ℝ→ℝ := fun s=>a.corrector (transportJoint μ s)
  let Q : ℝ→ℝ := fun s=>6*(conditionalGaussianEntropy μ (stdGaussian E) s).toReal-
    (boltzmannEntropy (transportPosition μ s)-boltzmannEntropy (positionGibbs U))
  have hμs (s:ℝ) : MemLp id 2 (transportJoint μ s) := transportProbability_memLp μ hμ s
  have hνs (s:ℝ) : MemLp id 2 (transportPosition μ s) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mpr
      (hμs s).fst
  have hνac (s:ℝ) : transportPosition μ s≪volume := by
    rw [transportPosition_eq_withDensity μ hac s]
    exact withDensity_absolutelyContinuous _ _
  have hCc : ContinuousOn C (Icc 0 T) :=
    (continuous_freeTransport_corrector μ a.targetProbability hμ a.position_memLp_two hac).continuousOn
  have hQc : Continuous Q := a.continuous_freeTransport_upper_rate μ hμ hK
  have hh := local_semiconcavity_integrated_corrector (W:=W) (C:=C) (Q:=Q)
    (M:=6*B^2) hT.le (lt_min hδ (by norm_num : (0:ℝ)<1)) hCc hQc ?_
  · dsimp only [C,Q] at hh
    simp only [transportJoint_zero] at hh
    rw [a.freeTransportRHS_integral_identity μ hμ hK hT] at hh
    exact hh
  · intro s hs t ht hst
    obtain ⟨F,r,hF,hmap,hr,hexp,hrB⟩ := hlocal s hs t ht (hst.trans (min_le_left _ _))
    have hb := QuadraticTransport.transported_cost_taylor
      (freePositionProbability μ s) a.targetProbability (freePositionProbability μ t)
      (hνs s) a.position_memLp_two (hνac s) hF hmap (hv s hs) (ha s hs) hr hexp
      (hst.trans (min_le_right _ _)) hB (hcost s hs) (hvB s hs) (haB s hs) hrB
    have hmcoef := a.mean_velocity_corrector (transportJoint μ s) (hμs s) (hνac s) (hmean s hs)
    change (∫x,⟪v s x,x-QuadraticTransport.brenierMap
      (freePositionProbability μ s) a.targetProbability x⟫ ∂transportPosition μ s)=C s at hmcoef
    change W t≤W s+(t-s)*(∫x,⟪v s x,x-QuadraticTransport.brenierMap
      (freePositionProbability μ s) a.targetProbability x⟫ ∂transportPosition μ s)+
      ((t-s)^2/2)*((∫x,‖v s x‖^2 ∂transportPosition μ s)+
      (∫x,⟪acc s x,x-positionBrenierMap (transportJoint μ s) a.targetProbability x⟫
        ∂transportPosition μ s))+6*B^2*|t-s|^3 at hb
    rw [hmcoef] at hb
    have hq := mul_le_mul_of_nonneg_left (hrate s hs)
      (div_nonneg (sq_nonneg (t-s)) (by norm_num : (0:ℝ)≤2))
    change _≤((t-s)^2/2)*Q s at hq
    linarith

end PersistencePays
#print axioms PersistencePays.A1.free_transport_of_local_mean_maps
