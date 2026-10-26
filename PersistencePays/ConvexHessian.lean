import PersistencePays.ProximalDerivative
import Mathlib.Algebra.QuadraticDiscriminant

/-! The a.e. derivative of a finite convex gradient is positive self-adjoint.
Full-measure sets suffice for uniqueness of the relative derivative. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem uniqueDiffWithinAt_of_full_measure (ρ : Measure E) [IsAddHaarMeasure ρ]
    {s : Set E} (hs : ρ sᶜ=0) (x : E) : UniqueDiffWithinAt ℝ s x := by
  have hd : Dense s := Measure.dense_of_ae (mem_ae_iff.mpr hs)
  apply UniqueDiffWithinAt.of_closure
  rw [hd.closure_eq]
  exact uniqueDiffWithinAt_univ

theorem convex_gradient_positive_derivative_ae (ρ : Measure E) [IsAddHaarMeasure ρ]
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂ρ, DifferentiableAt ℝ f x ∧ ∃ G : E →L[ℝ] E,
      HasFDerivWithinAt (gradient f) G {y | DifferentiableAt ℝ f y} x ∧
      G.toLinearMap.IsPositive := by
  have hbad : ∀ᵐ x ∂ρ, x ∉ proximalMap f hf '' proximalBad f hf := by
    apply ae_iff.mpr
    convert proximal_bad_image_null ρ f hf using 1
    congr 1
    ext x
    simp
  filter_upwards [convexOn_ae_differentiable ρ hf,hbad] with x hx hxb
  have hfx := (hx (mem_univ x)).2
  let D : Set E := {y | DifferentiableAt ℝ f y}
  let Q : E → E := fun y => y+gradient f y
  let P := proximalMap f hf
  have hPQ : P (Q x)=x := proximalMap_gradient_inverse hf hfx
  have hregular : Q x ∉ proximalBad f hf := fun h => hxb ⟨Q x,h,hPQ⟩
  have hdP : DifferentiableAt ℝ P (Q x) := by
    by_contra hn
    exact hregular (Or.inl hn)
  have hdet : (fderiv ℝ P (Q x)).det≠0 := fun hn => hregular (Or.inr ⟨hdP,hn⟩)
  let A : E ≃L[ℝ] E := (fderiv ℝ P (Q x)).toContinuousLinearEquivOfDetNeZero hdet
  have hA : HasFDerivAt P (A : E →L[ℝ] E) (Q x) := by simpa [A] using hdP.hasFDerivAt
  have hQc : ContinuousWithinAt Q D x :=
    continuousWithinAt_id.add (convex_gradient_continuousWithinAt hf hfx)
  have hinv : HasFDerivWithinAt Q (A.symm : E →L[ℝ] E) D x := by
    apply hA.hasFDerivWithinAt.of_local_left_inverse (t:=univ)
      (by simpa using hQc.tendsto) hfx
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact proximalMap_gradient_inverse hf hy
  have hsub := hinv.sub (hasFDerivWithinAt_id x D)
  have he : (fun y => Q y-y)=gradient f := by funext y; dsimp [Q]; abel
  change HasFDerivWithinAt (fun y => Q y-y) _ D x at hsub
  rw [he] at hsub
  exact ⟨hfx,_,hsub,inverse_proximal_derivative_positive f hf hdP hdet⟩

theorem convex_representative_fderiv_positive (ρ : Measure E) [IsAddHaarMeasure ρ]
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) {T : E → E} {s : Set E}
    (hs : ρ sᶜ=0) (hD : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hT : ∀ x ∈ s, T x=gradient f x) :
    ∀ᵐ x ∂ρ, (fderivWithin ℝ T s x).toLinearMap.IsPositive := by
  filter_upwards [convex_gradient_positive_derivative_ae ρ f hf,mem_ae_iff.mpr hs]
    with x hx hxs
  obtain ⟨G,hG,hpos⟩ := hx.2
  have hG' := (hG.mono (fun y hy => hD y hy)).congr (fun y hy => hT y hy) (hT x hxs)
  have he := hG'.fderivWithin (uniqueDiffWithinAt_of_full_measure ρ hs x)
  rwa [he]

/-- A positive operator with nonzero determinant is strictly positive. -/
theorem positive_inner_pos_of_det_ne_zero (G : E →L[ℝ] E)
    (hG : G.toLinearMap.IsPositive) (hdet : G.det≠0) {x : E} (hx : x≠0) :
    0 < ⟪x,G x⟫ := by
  have hnon : 0 ≤ ⟪x,G x⟫ := hG.re_inner_nonneg_right x
  apply lt_of_le_of_ne hnon
  intro he
  have he' : ⟪G x,x⟫=0 := by rw [real_inner_comm]; exact he.symm
  have hpoly : ∀ t : ℝ, 0 ≤ ⟪G (G x),G x⟫*(t*t) + (2*‖G x‖^2)*t+0 := by
    intro t
    have hh := hG.re_inner_nonneg_left (x+t•G x)
    change 0 ≤ ⟪G (x+t•G x),x+t•G x⟫ at hh
    simp only [map_add,map_smul,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right] at hh
    simp only [conj_trivial] at hh
    have hsym := hG.isSymmetric x (G x)
    change ⟪G x,G x⟫=⟪x,G (G x)⟫ at hsym
    have hcomm := real_inner_comm x (G (G x))
    rw [real_inner_self_eq_norm_sq] at hh hsym
    rw [he',hcomm,← hsym] at hh
    nlinarith only [hh]
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  have hb : (2*‖G x‖^2)^2=0 := le_antisymm (by nlinarith [hd]) (sq_nonneg _)
  have hb0 := sq_eq_zero_iff.mp hb
  have hn : ‖G x‖=0 := by nlinarith [norm_nonneg (G x),sq_nonneg ‖G x‖]
  have hz : G x=0 := norm_eq_zero.mp hn
  let A := G.toContinuousLinearEquivOfDetNeZero hdet
  have ha : A x=A 0 := by simpa [A] using hz
  exact hx (A.injective ha)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.convex_representative_fderiv_positive
#print axioms PersistencePays.QuadraticTransport.positive_inner_pos_of_det_ne_zero
