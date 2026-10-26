import PersistencePays.ConvexProximal
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Topology.Sequences

/-! Supporting gradients and their continuity on the differentiability set of
a finite convex function. No continuous differentiability assumption is made. -/
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem convex_gradient_supports {f : E → ℝ} (hf : ConvexOn ℝ univ f) {x : E}
    (hx : DifferentiableAt ℝ f x) : Supports f x (gradient f x) := by
  intro y
  have hc := hf.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasDerivAt (fun t : ℝ => f (AffineMap.lineMap x y t))
      ((fderiv ℝ f x) (y-x)) 0 := by
    have hx' : HasFDerivAt f (fderiv ℝ f x) (AffineMap.lineMap x y (0:ℝ)) := by simpa using hx.hasFDerivAt
    exact hx'.comp_hasDerivAt 0 AffineMap.hasDerivAt_lineMap
  have hh := hc.le_slope_of_hasDerivAt (by simp) (by simp) (by norm_num : (0:ℝ)<1) hd
  simp only [slope, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, inv_one, one_smul, vsub_eq_sub] at hh
  rw [← inner_gradient_left] at hh
  linarith

lemma norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [← toDual_gradient]
  exact ((InnerProductSpace.toDual ℝ E).norm_map _).symm

theorem convex_gradient_locally_bounded {f : E → ℝ} (hf : ConvexOn ℝ univ f) (x : E) :
    ∃ K : ℝ≥0, ∀ᶠ y in 𝓝 x, ‖gradient f y‖ ≤ K := by
  obtain ⟨K,s,hs,hl⟩ := hf.locallyLipschitz x
  refine ⟨K,?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mpr hs |> isOpen_interior.mem_nhds] with y hy
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitzOn ℝ (mem_interior_iff_mem_nhds.mp hy) hl

/-- Gradients of a finite convex function are continuous relative to its
possibly non-open differentiability set. This is not global C1 regularity. -/
theorem convex_gradient_continuousWithinAt {f : E → ℝ} (hf : ConvexOn ℝ univ f) {x : E}
    (hx : DifferentiableAt ℝ f x) :
    ContinuousWithinAt (gradient f) {y | DifferentiableAt ℝ f y} x := by
  have hfc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  obtain ⟨K,hK⟩ := convex_gradient_locally_bounded hf x
  apply (isCompact_closedBall (0:E) (K:ℝ)).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [nhdsWithin_le_nhds hK] with y hy
    simpa [Metric.mem_closedBall,dist_zero_right] using hy
  · intro v _ hv
    obtain ⟨u,hu,hvu⟩ := Filter.exists_seq_comp_tendsto hv
    have hu' : Tendsto u atTop (𝓝 x) := hu.mono_right nhdsWithin_le_nhds
    have hD := hu.eventually self_mem_nhdsWithin
    have hvSupport : Supports f x v := by
      intro z
      have hineq : ∀ᶠ n in atTop,
          f (u n)+⟪gradient f (u n),z-u n⟫ ≤ f z := by
        filter_upwards [hD] with n hn
        exact convex_gradient_supports hf hn z
      have hlim : Tendsto (fun n => f (u n)+⟪gradient f (u n),z-u n⟫) atTop
          (𝓝 (f x+⟪v,z-x⟫)) :=
        (hfc.continuousAt.tendsto.comp hu').add (hvu.inner (tendsto_const_nhds.sub hu'))
      exact le_of_tendsto hlim hineq
    exact supporting_vector_eq_gradient (s:=univ) (by simp) hx (fun z _ => hvSupport z)

theorem proximalMap_gradient_inverse {f : E → ℝ} (hf : ConvexOn ℝ univ f) {x : E}
    (hx : DifferentiableAt ℝ f x) : proximalMap f hf (x+gradient f x)=x := by
  apply (proximalMap_eq_iff f hf _ x).mpr
  simpa using convex_gradient_supports hf hx

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.convex_gradient_continuousWithinAt
