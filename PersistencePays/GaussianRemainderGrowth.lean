import PersistencePays.GaussianMeanField
import PersistencePays.CompactPosteriorJointBounds
import PersistencePays.CompactCoefficientBounds
import PersistencePays.AffineTimeGrowth

/-! Polynomial bounds for the actual full time-position derivatives of the
Gaussian-mixture conditional mean. Constants may depend on the smoothing scale. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped InnerProductSpace
universe u
variable {E Z:Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
local instance gaussianRemainderProdGroup : NormedAddCommGroup (ℝ×E) := inferInstance
local instance gaussianRemainderProdSpace : NormedSpace ℝ (ℝ×E) := inferInstance
local instance gaussianRemainderOperatorGroup : NormedAddCommGroup (ℝ×E→L[ℝ]E) := inferInstance
local instance gaussianRemainderFunctionalGroup : NormedAddCommGroup (ℝ×E→L[ℝ]ℝ) := inferInstance

theorem gaussianMeanRemainder_joint_growth (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (a b:ℝ) :
    ∃ C:ℝ, 1≤C ∧ ∀s∈Icc a b,∀y:E,
      ‖gaussianMeanRemainder μ g ε s y‖≤C ∧
      ‖fderiv ℝ (gaussianMeanRemainder μ g ε).uncurry (s,y)‖≤C*(1+‖y‖) ∧
      ‖fderiv ℝ (fderiv ℝ (gaussianMeanRemainder μ g ε).uncurry) (s,y)‖≤C*(1+‖y‖)^2 := by
  let ψ:((ℝ×E)×(E×E))→ℝ:=fun p=>regressionExponent ε p.1.1 (p.1.2,p.2)
  let F:((ℝ×E)×(E×E))→E:=fun p=>regressionLatentMean p.1.1 p.2
  have hproj:ContDiff ℝ 3 (fun p:((ℝ×E)×(E×E))=>(p.1.1,p.2)):=
    contDiff_fst.fst.prodMk contDiff_snd
  have hψ:ContDiff ℝ 3 ψ:=
    (((regressionScore_contDiff 3 hε).comp hproj).inner ℝ contDiff_fst.snd).add
      ((regressionLogWeight_contDiff 3 hε).comp hproj)
  have hF:ContDiff ℝ 3 F:=(regressionLatentMean_contDiff 3).comp hproj
  obtain ⟨A,hA,bA⟩:=compact_coefficient_c2_bounds (regressionLatentMean_contDiff (E:=E) 3) g hg a b
  obtain ⟨B,hB,bB⟩:=compact_coefficient_c2_bounds (regressionScore_contDiff (E:=E) 3 hε) g hg a b
  obtain ⟨D,hD,bD⟩:=compact_coefficient_c2_bounds (regressionLogWeight_contDiff (E:=E) 3 hε) g hg a b
  let J:ℝ:=2*‖(innerSL ℝ:E→L[ℝ]E→L[ℝ]ℝ)‖*B+D
  have hJ:0≤J:=by dsimp [J]; positivity
  let C:ℝ:=1+A+(A+2*A*J)+(A+6*A*J+6*A*J^2)
  have hC:1≤C:=by dsimp [C]; nlinarith [mul_nonneg hA.le hJ,mul_nonneg hA.le (sq_nonneg J)]
  refine ⟨C,hC,?_⟩
  intro s hs y
  have hFF(z:Z):ContDiff ℝ 2 (fun t=>regressionLatentMean t (g z)):=
    (regressionLatentMean_contDiff 2).comp (contDiff_id.prodMk contDiff_const)
  have hHH(z:Z):ContDiff ℝ 2 (fun t=>regressionScore ε t (g z)):=
    (regressionScore_contDiff 2 hε).comp (contDiff_id.prodMk contDiff_const)
  have hKK(z:Z):ContDiff ℝ 2 (fun t=>regressionLogWeight ε t (g z)):=
    (regressionLogWeight_contDiff 2 hε).comp (contDiff_id.prodMk contDiff_const)
  have bF0:∀z,‖F ((s,y),g z)‖≤A:=fun z=>(bA s hs z).1
  have bF12(z:Z):
      ‖fderiv ℝ (fun p:ℝ×E=>F (p,g z)) (s,y)‖≤A ∧
      ‖fderiv ℝ (fderiv ℝ (fun p:ℝ×E=>F (p,g z))) (s,y)‖≤A:=
    time_only_derivative_bounds (hFF z) (s,y) hA.le (bA s hs z).2.1 (bA s hs z).2.2
  have bψ12(z:Z):
      ‖fderiv ℝ (fun p:ℝ×E=>ψ (p,g z)) (s,y)‖≤J*(1+‖y‖) ∧
      ‖fderiv ℝ (fderiv ℝ (fun p:ℝ×E=>ψ (p,g z))) (s,y)‖≤J*(1+‖y‖):=
    affine_time_add_derivative_bounds (innerSL ℝ) (hHH z) (hKK z) (s,y) hB.le hD.le
      (bB s hs z).1 (bB s hs z).2.1 (bB s hs z).2.2
      (bD s hs z).2.1 (bD s hs z).2.2
  have hn:=compactPosteriorMean_joint_derivative_bounds μ g hg ψ hψ F hF (s,y)
    hA.le hJ (by linarith [norm_nonneg y]) bF0 (fun z=>(bF12 z).1)
    (fun z=>(bF12 z).2) (fun z=>(bψ12 z).1) (fun z=>(bψ12 z).2)
  have h0:‖gaussianMeanRemainder μ g ε s y‖≤A:=
    compactPosteriorMean_norm_le μ g hg ψ hψ.continuous F (s,y) A bF0
  have hAC:A≤C:=by dsimp [C]; nlinarith [mul_nonneg hA.le hJ,mul_nonneg hA.le (sq_nonneg J)]
  have h1C:A+2*A*J≤C:=by dsimp [C]; nlinarith [mul_nonneg hA.le hJ,mul_nonneg hA.le (sq_nonneg J)]
  have h2C:A+6*A*J+6*A*J^2≤C:=by dsimp [C]; nlinarith [mul_nonneg hA.le hJ,mul_nonneg hA.le (sq_nonneg J)]
  exact ⟨h0.trans hAC,hn.1.trans (mul_le_mul_of_nonneg_right h1C (by positivity)),
    hn.2.trans (mul_le_mul_of_nonneg_right h2C (by positivity))⟩
end PersistencePays
#print axioms PersistencePays.gaussianMeanRemainder_joint_growth
