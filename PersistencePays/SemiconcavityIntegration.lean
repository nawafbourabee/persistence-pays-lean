import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The scalar passage from the two-sided coupling expansion (A.6) to an
integrated corrector inequality. This is a calculus component; constructing
the actual mean-flow coupling is a separate obligation. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set Filter
open scoped Topology

theorem semiconcavity_corrector_increment {W C Q : ℝ → ℝ} {M x y : ℝ}
    (hxy : x < y)
    (hforward : W y ≤ W x+(y-x)*C x+(y-x)^2/2*Q x+M*|y-x|^3)
    (hbackward : W x ≤ W y+(x-y)*C y+(x-y)^2/2*Q y+M*|x-y|^3) :
    C y-C x ≤ (y-x)/2*(Q x+Q y)+2*M*(y-x)^2 := by
  rw [abs_of_pos (sub_pos.mpr hxy)] at hforward
  rw [abs_of_neg (sub_neg.mpr hxy)] at hbackward
  apply (le_of_mul_le_mul_left (a:=y-x) _ (sub_pos.mpr hxy))
  nlinarith

theorem corrector_increment_integral {C Q : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b)) (hQ : Continuous Q)
    (hinc : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y →
      C y-C x ≤ (y-x)/2*(Q x+Q y)+2*M*(y-x)^2) :
    C b-C a ≤ ∫ s in a..b, Q s := by
  let B : ℝ → ℝ := fun x => C a+∫ s in a..x, Q s
  have hBd (x : ℝ) : HasDerivAt B (Q x) x := by
    simpa only [B,zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable a x)
        hQ.stronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt).const_add (C a)
  have hBc : Continuous B := continuous_iff_continuousAt.mpr (fun x => (hBd x).continuousAt)
  have hbound : ∀ x ∈ Ico a b, ∀ r, Q x < r → ∃ᶠ y in 𝓝[>] x, slope C x y < r := by
    intro x hx r hr
    have hx' : x ∈ Icc a b := ⟨hx.1,hx.2.le⟩
    have hlim : Tendsto (fun y => (Q x+Q y)/2+2*M*(y-x)) (𝓝[>] x) (𝓝 (Q x)) := by
      have ht : Tendsto (fun y => (Q x+Q y)/2+2*M*(y-x)) (𝓝 x)
          (𝓝 ((Q x+Q x)/2+2*M*(x-x))) :=
        ((tendsto_const_nhds.add (hQ.continuousAt : ContinuousAt Q x)).div_const 2).add
          ((tendsto_id.sub_const x).const_mul (2*M))
      have ht' : Tendsto (fun y => (Q x+Q y)/2+2*M*(y-x)) (𝓝[>] x)
          (𝓝 ((Q x+Q x)/2+2*M*(x-x))) := ht.mono_left nhdsWithin_le_nhds
      convert ht' using 1 <;> congr 1 <;> ring
    have hsmall := hlim.eventually (gt_mem_nhds hr)
    have hupper : ∀ᶠ y in 𝓝[>] x, y < b :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2)
    have hall : ∀ᶠ y in 𝓝[>] x, slope C x y < r := by
      filter_upwards [self_mem_nhdsWithin,hupper,hsmall] with y hy hyb hys
      have hxy : x<y := hy
      have hi := hinc x hx' y ⟨hx.1.trans hxy.le,hyb.le⟩ hxy
      have hs : slope C x y ≤ (Q x+Q y)/2+2*M*(y-x) := by
        rw [slope_def_field]
        apply (div_le_iff₀ (sub_pos.mpr hxy)).mpr
        nlinarith
      exact hs.trans_lt hys
    exact hall.frequently
  have ht := image_le_of_liminf_slope_right_le_deriv_boundary hC
    (B:=B) (B':=Q) (by simp [B]) hBc.continuousOn
    (fun x _ => (hBd x).hasDerivWithinAt) hbound (show b ∈ Icc a b from ⟨hab,le_rfl⟩)
  dsimp only [B] at ht
  linarith

theorem semiconcavity_integrated_corrector {W C Q : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hC : ContinuousOn C (Icc a b)) (hQ : Continuous Q)
    (hexp : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      W y ≤ W x+(y-x)*C x+(y-x)^2/2*Q x+M*|y-x|^3) :
    C b-C a ≤ ∫ s in a..b, Q s := by
  apply corrector_increment_integral hab hC hQ
  intro x hx y hy hxy
  exact semiconcavity_corrector_increment hxy (hexp x hx y hy) (hexp y hy x hx)

end PersistencePays
#print axioms PersistencePays.semiconcavity_integrated_corrector
