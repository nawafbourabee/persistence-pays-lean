import PersistencePays.ConvexDivergence

/-! Uniform bounds on convex gradients on bounded sets, including their
possibly discontinuous representatives. -/
open Set MeasureTheory Metric
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem convex_gradient_bound_ball {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ) (R : ℝ) :
    ∃ C : ℝ≥0,∀ x:E,‖x‖≤R → ‖gradient φ x‖≤C := by
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hb : Bornology.IsBounded (φ '' ball (0:E) (R+2)) :=
    ((isCompact_closedBall (0:E) (R+2)).image hc).isBounded.subset
      (image_mono ball_subset_closedBall)
  obtain ⟨C,hC⟩ := (hφ.subset (subset_univ _) (convex_ball (0:E) (R+2))).exists_lipschitzOnWith_of_isBounded
    (show R+1<R+2 by linarith) hb
  refine ⟨C,fun x hx => ?_⟩
  rw [norm_gradient_eq_norm_fderiv]
  apply norm_fderiv_le_of_lipschitzOn ℝ _ hC
  apply isOpen_ball.mem_nhds
  rw [mem_ball_zero_iff]
  linarith

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.convex_gradient_bound_ball
