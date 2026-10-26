import PersistencePays.ConvexDivergence
import PersistencePays.SymmetricPositiveTrace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Local integrability of the actual positive Hessian field is derived from
compact scalar divergence, rather than assumed as part of the transport map. -/
open Set Filter MeasureTheory Metric
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem convex_hessian_locallyIntegrable
    {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ)
    {T : E → E} (he : T =ᵐ[volume] gradient φ)
    {G : E → E →L[ℝ] E} {s : Set E}
    (hs : volume sᶜ=0) (hG : Measurable G)
    (hd : ∀ᵐ x ∂volume,HasFDerivWithinAt T (G x) s x)
    (hpos : ∀ᵐ x ∂volume,(G x).toLinearMap.IsPositive) :
    LocallyIntegrable G volume := by
  have hq : LocallyIntegrable (fun x => (G x).toLinearMap.trace ℝ E) volume := by
    intro x
    let η : ContDiffBump x := ⟨1,2,by norm_num,by norm_num⟩
    have hi := (compact_convex_divergence hφ he hs hG hd
      (hpos.mono (fun _ hx => hx.re_inner_nonneg_right))
      (η.contDiff (n:=1)) η.hasCompactSupport (fun _ => η.nonneg)).1
    refine ⟨ball x 1,ball_mem_nhds x zero_lt_one,?_⟩
    apply hi.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hη : η y=1 := η.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp only [hη,one_mul]
  apply hq.mono hG.aestronglyMeasurable
  filter_upwards [hpos] with x hx
  exact (positive_norm_le_trace (G x) hx).trans (le_abs_self _)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.convex_hessian_locallyIntegrable
