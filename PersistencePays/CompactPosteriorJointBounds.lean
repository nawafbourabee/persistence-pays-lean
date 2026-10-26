import PersistencePays.CompactPosteriorSecondDerivative
import PersistencePays.CompactPosteriorSmooth
import PersistencePays.ParameterDerivativeSmooth

noncomputable section
namespace PersistencePays
open MeasureTheory
universe u
variable {P Y Z V:Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compactPosteriorMean_joint_derivative_bounds (μ:Measure Z) [IsProbabilityMeasure μ]
    (g:Z→Y) (hg:Continuous g) (ψ:P×Y→ℝ) (hψ:ContDiff ℝ 3 ψ)
    (F:P×Y→V) (hF:ContDiff ℝ 3 F) (x:P) {A B w:ℝ}
    (hA:0≤A) (hB:0≤B) (hw:1≤w)
    (bF:∀z,‖F (x,g z)‖≤A)
    (bF':∀z,‖fderiv ℝ (fun p=>F (p,g z)) x‖≤A)
    (bF'':∀z,‖fderiv ℝ (fderiv ℝ (fun p=>F (p,g z))) x‖≤A)
    (bψ':∀z,‖fderiv ℝ (fun p=>ψ (p,g z)) x‖≤B*w)
    (bψ'':∀z,‖fderiv ℝ (fderiv ℝ (fun p=>ψ (p,g z))) x‖≤B*w) :
    ‖fderiv ℝ (compactPosteriorMean μ g ψ F) x‖≤(A+2*A*B)*w ∧
    ‖fderiv ℝ (fderiv ℝ (compactPosteriorMean μ g ψ F)) x‖≤(A+6*A*B+6*A*B^2)*w^2 := by
  let ψ₀:P→Z→ℝ:=fun p z=>ψ (p,g z)
  let F₀:P→Z→V:=fun p z=>F (p,g z)
  let ψ₁:P→Z→P→L[ℝ]ℝ:=fun p z=>fderiv ℝ (fun q=>ψ (q,g z)) p
  let F₁:P→Z→P→L[ℝ]V:=fun p z=>fderiv ℝ (fun q=>F (q,g z)) p
  let ψ₂:P→Z→P→L[ℝ]P→L[ℝ]ℝ:=fun p z=>fderiv ℝ (fderiv ℝ (fun q=>ψ (q,g z))) p
  let F₂:P→Z→P→L[ℝ]P→L[ℝ]V:=fun p z=>fderiv ℝ (fderiv ℝ (fun q=>F (q,g z))) p
  have hp:Continuous (fun p:P×Z=>(p.1,g p.2)):=continuous_fst.prodMk (hg.comp continuous_snd)
  have hcψ:Continuous ψ₀.uncurry:=hψ.continuous.comp hp
  have hcF:Continuous F₀.uncurry:=hF.continuous.comp hp
  have hψ₁:ContDiff ℝ 2 (fun p:P×Y=>fderiv ℝ (fun q=>ψ (q,p.2)) p.1):=
    parameter_fderiv_contDiff (by convert hψ using 1 <;> norm_num)
  have hF₁:ContDiff ℝ 2 (fun p:P×Y=>fderiv ℝ (fun q=>F (q,p.2)) p.1):=
    parameter_fderiv_contDiff (by convert hF using 1 <;> norm_num)
  have hcψ₁:Continuous ψ₁.uncurry:=hψ₁.continuous.comp hp
  have hcF₁:Continuous F₁.uncurry:=hF₁.continuous.comp hp
  have hcψ₂:Continuous ψ₂.uncurry:=
    (parameter_second_fderiv_contDiff (n:=1) (by convert hψ using 1 <;> norm_num)).continuous.comp hp
  have hcF₂:Continuous F₂.uncurry:=
    (parameter_second_fderiv_contDiff (n:=1) (by convert hF using 1 <;> norm_num)).continuous.comp hp
  have hdψ:∀p z,HasFDerivAt (fun q=>ψ₀ q z) (ψ₁ p z) p:=by
    intro p z
    exact ((hψ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p).hasFDerivAt
  have hdF:∀p z,HasFDerivAt (fun q=>F₀ q z) (F₁ p z) p:=by
    intro p z
    exact ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p).hasFDerivAt
  have hdψ₁:∀p z,HasFDerivAt (fun q=>ψ₁ q z) (ψ₂ p z) p:=by
    intro p z
    exact ((hψ₁.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p).hasFDerivAt
  have hdF₁:∀p z,HasFDerivAt (fun q=>F₁ q z) (F₂ p z) p:=by
    intro p z
    exact ((hF₁.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num) p).hasFDerivAt
  have hn₁:=compactWeightedMean_fderiv_norm μ hcψ hcF hcψ₁ hcF₁ hdψ hdF x
    hA (mul_nonneg hB (by linarith)) hA bF bψ' bF'
  have hn₂:=compactWeightedMean_second_fderiv_norm μ hcψ hcF hcψ₁ hcF₁ hcψ₂ hcF₂
    hdψ hdF hdψ₁ hdF₁ x hA (mul_nonneg hB (by linarith)) hA hA
    (mul_nonneg hB (by linarith)) bF bψ' bF' bψ'' bF''
  have hw2:1≤w^2:=by nlinarith
  have hww:w≤w^2:=by nlinarith
  constructor
  · exact hn₁.trans (by nlinarith [mul_le_mul_of_nonneg_left hw hA])
  · apply hn₂.trans
    nlinarith [mul_le_mul_of_nonneg_left hw2 hA,
      mul_le_mul_of_nonneg_left hww (mul_nonneg hA hB)]
end PersistencePays
#print axioms PersistencePays.compactPosteriorMean_joint_derivative_bounds
