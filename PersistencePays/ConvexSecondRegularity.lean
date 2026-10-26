import PersistencePays.ConvexGradient
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! Almost-everywhere differentiability of the gradient on the full-measure
differentiability set of a finite convex function. The proof constructs the
proximal map and uses Rademacher plus the null-image form of the area theorem.
No Alexandrov or Brenier regularity theorem is assumed. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lipschitz_image_null (ρ : Measure E) [IsAddHaarMeasure ρ]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) {s : Set E} (hs : ρ s=0) :
    ρ (f '' s)=0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hH : H s=0 := (Measure.absolutelyContinuous_isAddHaarMeasure H ρ) hs
  have hi : H (f '' s)=0 := by
    have hh := hf.hausdorffMeasure_image_le (d:=(Module.finrank ℝ E : ℝ))
      (by positivity) s
    change H (f '' s) ≤ (K:ℝ≥0∞)^(Module.finrank ℝ E : ℝ)*H s at hh
    simpa [hH] using hh
  exact (Measure.absolutelyContinuous_isAddHaarMeasure ρ H) hi

def proximalBad (f : E → ℝ) (hf : ConvexOn ℝ univ f) : Set E :=
  {z | ¬DifferentiableAt ℝ (proximalMap f hf) z} ∪
  {z | DifferentiableAt ℝ (proximalMap f hf) z ∧
    (fderiv ℝ (proximalMap f hf) z).det=0}

theorem proximal_bad_image_null (ρ : Measure E) [IsAddHaarMeasure ρ]
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) :
    ρ (proximalMap f hf '' proximalBad f hf)=0 := by
  have hbad : ρ {z | ¬DifferentiableAt ℝ (proximalMap f hf) z}=0 :=
    ae_iff.mp ((proximalMap_lipschitz f hf).ae_differentiableAt (μ:=ρ))
  have h1 := lipschitz_image_null ρ (proximalMap_lipschitz f hf) hbad
  have h2 : ρ (proximalMap f hf '' {z | DifferentiableAt ℝ (proximalMap f hf) z ∧
      (fderiv ℝ (proximalMap f hf) z).det=0})=0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero ρ
      (fun z hz => hz.1.hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  rw [proximalBad,image_union,measure_union_null h1 h2]

theorem convex_gradient_ae_differentiableWithin (ρ : Measure E) [IsAddHaarMeasure ρ]
    (f : E → ℝ) (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂ρ, DifferentiableAt ℝ f x ∧
      DifferentiableWithinAt ℝ (gradient f) {y | DifferentiableAt ℝ f y} x := by
  have hbad : ∀ᵐ x ∂ρ, x ∉ proximalMap f hf '' proximalBad f hf :=
    ae_iff.mpr (by
      convert proximal_bad_image_null ρ f hf using 1
      congr 1
      ext x
      simp)
  filter_upwards [convexOn_ae_differentiable ρ hf,hbad] with x hx hxb
  have hfx := (hx (mem_univ x)).2
  refine ⟨hfx,?_⟩
  let D : Set E := {y | DifferentiableAt ℝ f y}
  let Q : E → E := fun y => y+gradient f y
  let P := proximalMap f hf
  have hPQ : P (Q x)=x := proximalMap_gradient_inverse hf hfx
  have hregular : Q x ∉ proximalBad f hf := by
    intro h
    exact hxb ⟨Q x,h,hPQ⟩
  have hdP : DifferentiableAt ℝ P (Q x) := by
    by_contra hn
    exact hregular (Or.inl hn)
  have hdet : (fderiv ℝ P (Q x)).det≠0 := by
    intro hn
    exact hregular (Or.inr ⟨hdP,hn⟩)
  let A : E ≃L[ℝ] E := (fderiv ℝ P (Q x)).toContinuousLinearEquivOfDetNeZero hdet
  have hA : HasFDerivAt P (A : E →L[ℝ] E) (Q x) := by
    simpa [A] using hdP.hasFDerivAt
  have hQc : ContinuousWithinAt Q D x :=
    continuousWithinAt_id.add (convex_gradient_continuousWithinAt hf hfx)
  have hinv : HasFDerivWithinAt Q (A.symm : E →L[ℝ] E) D x := by
    apply hA.hasFDerivWithinAt.of_local_left_inverse
      (t:=univ) (by simpa using hQc.tendsto) hfx
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact proximalMap_gradient_inverse hf hy
  have hsub := hinv.sub (hasFDerivWithinAt_id x D)
  have he : (fun y => Q y-y)=gradient f := by
    funext y
    dsimp [Q]
    abel
  change HasFDerivWithinAt (fun y => Q y-y) _ D x at hsub
  rw [he] at hsub
  exact hsub.differentiableWithinAt

/-- A measurable full-measure domain on which the genuine gradient is
differentiable. The derivative is relative to this domain, exactly as allowed
by the area formula. -/
theorem convex_gradient_measurable_differentiability_domain
    (ρ : Measure E) [IsAddHaarMeasure ρ] (f : E → ℝ) (hf : ConvexOn ℝ univ f) :
    ∃ s : Set E, MeasurableSet s ∧ ρ sᶜ=0 ∧
      (∀ x ∈ s, DifferentiableAt ℝ f x) ∧ DifferentiableOn ℝ (gradient f) s := by
  have ha := convex_gradient_ae_differentiableWithin ρ f hf
  obtain ⟨b,hb,hbm,hb0⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  have hp {x : E} (hx : x ∈ bᶜ) : DifferentiableAt ℝ f x ∧
      DifferentiableWithinAt ℝ (gradient f) {y | DifferentiableAt ℝ f y} x := by
    by_contra hn
    exact hx (hb hn)
  refine ⟨bᶜ,hbm.compl,by simpa using hb0,fun x hx => (hp hx).1,?_⟩
  intro x hx
  exact (hp hx).2.mono (fun y hy => (hp hy).1)

end
end PersistencePays.QuadraticTransport

#print axioms PersistencePays.QuadraticTransport.convex_gradient_ae_differentiableWithin
