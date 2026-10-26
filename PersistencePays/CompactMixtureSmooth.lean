import PersistencePays.CompactParameterIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Every finite derivative of a smooth mixture over compact latent data.
The latent law may be arbitrary, including singular and atomic laws. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
universe u
variable {P Y Z : Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compact_mixture_integral_contDiff (n : ℕ)
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure Z) [IsFiniteMeasure μ] (g : Z → Y) (hg : Continuous g)
    (F : P×Y → V) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => ∫ z, F (x,g z) ∂μ) := by
  induction n generalizing V with
  | zero =>
    apply contDiff_zero.mpr
    apply compact_parameter_integral_continuous
    exact hF.continuous.comp (continuous_fst.prodMk (hg.comp continuous_snd))
  | succ n ih =>
    obtain ⟨F',hF',hd⟩ := contDiff_succ_iff_hasFDerivAt.mp hF
    let G : P×Y → P →L[ℝ] V := fun q => (F' q).comp (ContinuousLinearMap.inl ℝ P Y)
    have hG : ContDiff ℝ n G := hF'.clm_comp contDiff_const
    have hGD := ih G hG
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ z, G (x,g z) ∂μ,hGD,?_⟩
    intro x
    apply compact_parameter_integral_hasFDerivAt μ
      (F:=fun x z => F (x,g z)) (F':=fun x z => G (x,g z))
    · exact hF.continuous.comp (continuous_fst.prodMk (hg.comp continuous_snd))
    · exact hG.continuous.comp (continuous_fst.prodMk (hg.comp continuous_snd))
    · intro y z
      have ht := (hd (y,g z)).comp y ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk
        (hasFDerivAt_const (𝕜:=ℝ) (g z) y))
      exact ht

theorem compact_mixture_integral_contDiff_real (n : ℕ)
    (μ : Measure Z) [IsFiniteMeasure μ] (g : Z → Y) (hg : Continuous g)
    (F : P×Y → ℝ) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => ∫ z, F (x,g z) ∂μ) := by
  let e : ULift.{u} ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.ulift
  have hl := compact_mixture_integral_contDiff n μ g hg (fun p => e.symm (F p))
    (e.symm.contDiff.comp hF)
  have hh := e.contDiff.comp hl
  have he (x:P) : e (∫ z, e.symm (F (x,g z)) ∂μ) = ∫ z, F (x,g z) ∂μ := by
    rw [← e.integral_comp_comm]
    simp only [e.apply_symm_apply]
  simpa only [Function.comp_def,he] using hh

end PersistencePays
#print axioms PersistencePays.compact_mixture_integral_contDiff
