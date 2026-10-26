import PersistencePays.GibbsTransportEntropy
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Smooth integration by parts for the actual Gibbs law. Its application to
coordinate functions proves the identity E⟨∇U(X),X⟩=d with all integrability
requirements derived from A1. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma A1.gibbs_weight_fderiv {U : E → ℝ} {m L : ℝ} (a : A1 U m L) (x v:E) :
    fderiv ℝ (fun y => Real.exp (-U y)) x v =
      -⟪gradient U x,v⟫_ℝ * Real.exp (-U x) := by
  change (fderiv ℝ (fun y => Real.exp ((-U) y)) x) v = _
  rw [((a.hasGradientAt x).hasFDerivAt.neg.exp).fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,
    InnerProductSpace.toDual_apply_apply,smul_eq_mul,Pi.neg_apply]
  ring

lemma A1.gibbs_integrable_iff_weighted {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (f:E→ℝ) : Integrable f (positionGibbs U) ↔
      Integrable (fun x => f x*Real.exp (-U x)) volume := by
  simpa only [positionGibbs,Pi.neg_apply,smul_eq_mul,mul_comm] using
    integrable_tilted_iff (f := -U) a.gibbs_integrable f

lemma gibbs_integral_weighted (U f:E→ℝ) :
    (∫ x,f x ∂positionGibbs U) =
      (∫ x,f x*Real.exp (-U x))/(∫ x,Real.exp (-U x)) := by
  rw [positionGibbs,integral_tilted]
  simp only [Pi.neg_apply,smul_eq_mul]
  have he : (fun x:E => (Real.exp (-U x)/(∫ y,Real.exp (-U y)))*f x) =
      (fun x:E => (f x*Real.exp (-U x))/(∫ y,Real.exp (-U y))) := by
    funext x
    ring
  rw [he,integral_div]

theorem A1.gibbs_integration_by_parts {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (f:E→ℝ) (hfd:Differentiable ℝ f) (v:E)
    (hif:Integrable f (positionGibbs U))
    (hid:Integrable (fun x => fderiv ℝ f x v) (positionGibbs U))
    (hix:Integrable (fun x => f x*⟪gradient U x,v⟫_ℝ) (positionGibbs U)) :
    (∫ x,f x*⟪gradient U x,v⟫_ℝ ∂positionGibbs U) =
      ∫ x,fderiv ℝ f x v ∂positionGibbs U := by
  have hwf := (a.gibbs_integrable_iff_weighted f).mp hif
  have hwd := (a.gibbs_integrable_iff_weighted (fun x => fderiv ℝ f x v)).mp hid
  have hwx := (a.gibbs_integrable_iff_weighted (fun x => f x*⟪gradient U x,v⟫_ℝ)).mp hix
  have hig : Integrable (fun x => f x*fderiv ℝ (fun y => Real.exp (-U y)) x v) volume := by
    simp_rw [a.gibbs_weight_fderiv]
    convert hwx.neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hwd hig hwf
    (fun x _ => hfd x)
    (fun x _ => ((a.hasGradientAt x).hasFDerivAt.neg.exp).differentiableAt)
  simp_rw [a.gibbs_weight_fderiv] at hb
  have he : (fun x => f x*(-⟪gradient U x,v⟫_ℝ *Real.exp (-U x))) =
      (fun x => -(f x*⟪gradient U x,v⟫_ℝ *Real.exp (-U x))) := by funext x; ring
  rw [he,integral_neg] at hb
  rw [gibbs_integral_weighted,gibbs_integral_weighted]
  congr 1
  linarith

theorem A1.gibbs_stein_coordinate {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (v:E) :
    (∫ x,⟪v,x⟫_ℝ *⟪gradient U x,v⟫_ℝ ∂positionGibbs U) = ‖v‖^2 := by
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hx := (innerSL ℝ v).comp_memLp' a.position_memLp_two
  have hg := (innerSL ℝ v).comp_memLp' (a.gradient_memLp a.position_memLp_two)
  have hprod : Integrable (fun x => ⟪v,x⟫_ℝ *⟪gradient U x,v⟫_ℝ) (positionGibbs U) := by
    apply (hx.integrable_mul hg).congr
    filter_upwards with x
    change ⟪v,x⟫_ℝ *⟪v,gradient U x⟫_ℝ = ⟪v,x⟫_ℝ *⟪gradient U x,v⟫_ℝ
    rw [real_inner_comm (gradient U x) v]
  have hd (x:E) : fderiv ℝ (fun y:E => ⟪v,y⟫_ℝ) x = innerSL ℝ v :=
    (innerSL ℝ v).hasFDerivAt.fderiv
  have hh := a.gibbs_integration_by_parts (fun x => ⟪v,x⟫_ℝ)
    (innerSL ℝ v).differentiable v (hx.integrable (by norm_num))
    (by simp only [hd]; exact integrable_const _) hprod
  simpa only [hd,innerSL_apply_apply,real_inner_self_eq_norm_sq,integral_const,
    probReal_univ,one_smul] using hh

theorem A1.gibbs_stein_identity {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    (∫ x,⟪gradient U x,x⟫_ℝ ∂positionGibbs U) = (Module.finrank ℝ E:ℝ) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have he (x:E) : ⟪gradient U x,x⟫_ℝ =
      ∑ i,⟪b i,x⟫_ℝ *⟪gradient U x,b i⟫_ℝ := by
    simpa only [mul_comm] using (b.sum_inner_mul_inner (gradient U x) x).symm
  simp_rw [he]
  rw [integral_finsetSum]
  · simp_rw [a.gibbs_stein_coordinate,b.norm_eq_one]
    simp
  · intro i _
    letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
    have hx := (innerSL ℝ (b i)).comp_memLp' a.position_memLp_two
    have hg := (innerSL ℝ (b i)).comp_memLp' (a.gradient_memLp a.position_memLp_two)
    apply (hx.integrable_mul hg).congr
    filter_upwards with x
    change ⟪b i,x⟫_ℝ *⟪b i,gradient U x⟫_ℝ = ⟪b i,x⟫_ℝ *⟪gradient U x,b i⟫_ℝ
    rw [real_inner_comm (gradient U x) (b i)]

end PersistencePays
#print axioms PersistencePays.A1.gibbs_integration_by_parts
#print axioms PersistencePays.A1.gibbs_stein_identity
