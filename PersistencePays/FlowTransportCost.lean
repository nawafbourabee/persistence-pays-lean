import PersistencePays.FlowCostExpansion
import PersistencePays.QuadraticDistance

/-! The actual endpoint coupling behind Appendix A.6. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace QuadraticTransport

theorem cost_le_transported_brenier (μ ν μ':ProbabilityMeasure E)
    (hμ:MemLp id 2 (μ:Measure E)) (hν:MemLp id 2 (ν:Measure E))
    (hac:(μ:Measure E)≪volume) {F:E→E} (hF:Measurable F)
    (hF2:MemLp F 2 (μ:Measure E)) (hmap:(μ:Measure E).map F=(μ':Measure E)) :
    (cost μ' ν).toReal≤∫x,‖F x-brenierMap μ ν x‖^2 ∂(μ:Measure E) := by
  let T := brenierMap μ ν
  have hT := brenierMap_spec μ ν hμ hν hac
  have hT2 := brenierMap_memLp μ ν hμ hν hac
  let π : ProbabilityMeasure (E×E) := ProbabilityMeasure.map μ (hF.prodMk hT.1).aemeasurable
  have hπ : π∈plans μ' ν := by
    constructor
    · apply Subtype.ext
      change ((μ:Measure E).map (fun x=>(F x,T x))).map Prod.fst=(μ':Measure E)
      rw [Measure.map_map measurable_fst (hF.prodMk hT.1)]
      exact hmap
    · apply Subtype.ext
      change ((μ:Measure E).map (fun x=>(F x,T x))).map Prod.snd=(ν:Measure E)
      rw [Measure.map_map measurable_snd (hF.prodMk hT.1)]
      exact hT.2.1
  have hμ' : MemLp id 2 (μ':Measure E) := by
    rw [←hmap]
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hF.aemeasurable).mpr hF2
  have hb := ENNReal.toReal_mono
    (squaredCost_finite μ' ν π hπ hμ'.integrable_norm_pow' hν.integrable_norm_pow')
    (show cost μ' ν ≤ squaredCost π from iInf₂_le π hπ)
  rw [squaredCost_toReal μ' ν π hπ hμ' hν] at hb
  have he : (∫z,‖z.1-z.2‖^2 ∂(π:Measure (E×E)))=
      ∫x,‖F x-T x‖^2 ∂(μ:Measure E) :=
    integral_map (hF.prodMk hT.1).aemeasurable (by fun_prop)
  exact he ▸ hb

/-- Uniform L² bounds and a cubic trajectory remainder give the genuine one-sided
second-order transport-cost estimate, with the same target Brenier map. -/
theorem transported_cost_taylor (μ ν μ':ProbabilityMeasure E)
    (hμ:MemLp id 2 (μ:Measure E)) (hν:MemLp id 2 (ν:Measure E))
    (hac:(μ:Measure E)≪volume) {F v a r:E→E} {θ B:ℝ}
    (hF:Measurable F) (hmap:(μ:Measure E).map F=(μ':Measure E))
    (hv:MemLp v 2 (μ:Measure E)) (ha:MemLp a 2 (μ:Measure E))
    (hr:MemLp r 2 (μ:Measure E))
    (hexp:∀x,F x=x+θ • v x+(θ^2/2) • a x+r x)
    (hθ:|θ|≤1) (hB:0≤B)
    (hξB:(cost μ ν).toReal≤B^2)
    (hvB:∫x,‖v x‖^2 ∂(μ:Measure E)≤B^2)
    (haB:∫x,‖a x‖^2 ∂(μ:Measure E)≤B^2)
    (hrB:∫x,‖r x‖^2 ∂(μ:Measure E)≤(B*|θ|^3)^2) :
    (cost μ' ν).toReal/2≤(cost μ ν).toReal/2+
      θ*(∫x,⟪v x,x-brenierMap μ ν x⟫ ∂(μ:Measure E))+
      (θ^2/2)*((∫x,‖v x‖^2 ∂(μ:Measure E))+
        (∫x,⟪a x,x-brenierMap μ ν x⟫ ∂(μ:Measure E)))+6*B^2*|θ|^3 := by
  have hF2 : MemLp F 2 (μ:Measure E) := by
    have heq : F=fun x=>x+θ • v x+(θ^2/2) • a x+r x := funext hexp
    rw [heq]
    exact ((hμ.add (hv.const_smul θ)).add (ha.const_smul (θ^2/2))).add hr
  have hT := brenierMap_memLp μ ν hμ hν hac
  have hξ : MemLp (fun x=>x-brenierMap μ ν x) 2 (μ:Measure E) := hμ.sub hT
  have hcost := brenierMap_displacement_cost μ ν hμ hν hac
  have hb := integral_quadratic_taylor_bound hθ hB hξ hv ha hr
    (hcost.trans_le hξB) hvB haB hrB
  have hp := cost_le_transported_brenier μ ν μ' hμ hν hac hF hF2 hmap
  have heq (x:E) : F x-brenierMap μ ν x=
      (x-brenierMap μ ν x)+θ • v x+(θ^2/2) • a x+r x := by
    rw [hexp]; abel
  simp_rw [heq] at hp
  rw [integral_div,hcost] at hb
  linarith

end QuadraticTransport
end PersistencePays
#print axioms PersistencePays.QuadraticTransport.cost_le_transported_brenier
#print axioms PersistencePays.QuadraticTransport.transported_cost_taylor
