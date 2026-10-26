import PersistencePays.CompactPosteriorCovariance
import PersistencePays.TensorDerivativeBound

/-! A second derivative bound for normalized compact posterior expectations.
All constants are independent of the posterior normalizer. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
variable {P Z V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem compactWeightedMean_second_fderiv_norm (μ:Measure Z) [IsProbabilityMeasure μ]
    {ψ:P→Z→ℝ} {F:P→Z→V} {ψ':P→Z→P→L[ℝ]ℝ} {F':P→Z→P→L[ℝ]V}
    {ψ'':P→Z→P→L[ℝ]P→L[ℝ]ℝ} {F'':P→Z→P→L[ℝ]P→L[ℝ]V}
    (hψ:Continuous ψ.uncurry) (hF:Continuous F.uncurry)
    (hψ':Continuous ψ'.uncurry) (hF':Continuous F'.uncurry)
    (hψ'':Continuous ψ''.uncurry) (hF'':Continuous F''.uncurry)
    (hdψ:∀x z,HasFDerivAt (fun y=>ψ y z) (ψ' x z) x)
    (hdF:∀x z,HasFDerivAt (fun y=>F y z) (F' x z) x)
    (hdψ':∀x z,HasFDerivAt (fun y=>ψ' y z) (ψ'' x z) x)
    (hdF':∀x z,HasFDerivAt (fun y=>F' y z) (F'' x z) x)
    (x:P) {A B C D J:ℝ} (hA:0≤A) (hB:0≤B) (hC:0≤C) (hD:0≤D) (hJ:0≤J)
    (bF:∀z,‖F x z‖≤A) (bψ':∀z,‖ψ' x z‖≤B) (bF':∀z,‖F' x z‖≤C)
    (bψ'':∀z,‖ψ'' x z‖≤J) (bF'':∀z,‖F'' x z‖≤D) :
    ‖fderiv ℝ (fderiv ℝ (compactWeightedMean μ ψ F)) x‖≤D+4*B*C+2*A*J+6*A*B^2 := by
  let T:P→Z→P→L[ℝ]V:=fun y z=>(ψ' y z).smulRight (F y z)
  let T':P→Z→P→L[ℝ]P→L[ℝ]V:=fun y z=>tensorDerivative (ψ' y z) (F y z) (ψ'' y z) (F' y z)
  have hT:Continuous T.uncurry:=
    (ContinuousLinearMap.smulRightL ℝ P V).continuous₂.comp₂ hψ' hF
  have hT':Continuous T'.uncurry:=
    (((ContinuousLinearMap.smulRightL ℝ P V).precompR P).continuous₂.comp₂ hψ' hF').add
      (((ContinuousLinearMap.smulRightL ℝ P V).precompL P).continuous₂.comp₂ hψ'' hF)
  have hdT:∀y z,HasFDerivAt (fun u=>T u z) (T' y z) y:=
    fun y z=>tensor_hasFDerivAt (hdψ' y z) (hdF y z)
  have bT(z:Z):‖T x z‖≤B*A := by
    change ‖(ψ' x z).smulRight (F x z)‖≤_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bψ' z) (bF z) (norm_nonneg _) hB
  have bT'(z:Z):‖T' x z‖≤B*C+J*A :=
    (tensorDerivative_norm_le _ _ _ _).trans (add_le_add
      (mul_le_mul (bψ' z) (bF' z) (norm_nonneg _) hB)
      (mul_le_mul (bψ'' z) (bF z) (norm_nonneg _) hJ))
  have hf:Differentiable ℝ (compactWeightedMean μ ψ F):=fun y=>
    (compactWeightedMean_hasFDerivAt μ hψ hF hψ' hF' hdψ hdF y).differentiableAt
  have hf':Differentiable ℝ (compactWeightedMean μ ψ F'):=fun y=>
    (compactWeightedMean_hasFDerivAt μ hψ hF' hψ' hF'' hdψ hdF' y).differentiableAt
  have ht:Differentiable ℝ (compactWeightedMean μ ψ T):=fun y=>
    (compactWeightedMean_hasFDerivAt μ hψ hT hψ' hT' hdψ hdT y).differentiableAt
  have hr:Differentiable ℝ (compactWeightedMean μ ψ ψ'):=fun y=>
    (compactWeightedMean_hasFDerivAt μ hψ hψ' hψ' hψ'' hdψ hdψ' y).differentiableAt
  let Q:P→P→L[ℝ]V:=fun y=>(compactWeightedMean μ ψ ψ' y).smulRight (compactWeightedMean μ ψ F y)
  have hq:HasFDerivAt Q
      (tensorDerivative (compactWeightedMean μ ψ ψ' x) (compactWeightedMean μ ψ F x)
        (fderiv ℝ (compactWeightedMean μ ψ ψ') x) (fderiv ℝ (compactWeightedMean μ ψ F) x)) x :=
    tensor_hasFDerivAt (hr x).hasFDerivAt (hf x).hasFDerivAt
  have heq:fderiv ℝ (compactWeightedMean μ ψ F)=fun y=>
      compactWeightedMean μ ψ F' y+compactWeightedMean μ ψ T y-Q y := by
    funext y
    exact compactWeightedMean_fderiv_covariance μ hψ hF hψ' hF' hdψ hdF y
  have hnf:=compactWeightedMean_fderiv_norm μ hψ hF hψ' hF' hdψ hdF x hA hB hC bF bψ' bF'
  have hnf':=compactWeightedMean_fderiv_norm μ hψ hF' hψ' hF'' hdψ hdF' x hC hB hD bF' bψ' bF''
  have hnt:=compactWeightedMean_fderiv_norm μ hψ hT hψ' hT' hdψ hdT x
    (mul_nonneg hB hA) hB (by positivity) bT bψ' bT'
  have hnr:=compactWeightedMean_fderiv_norm μ hψ hψ' hψ' hψ'' hdψ hdψ' x hB hB hJ bψ' bψ' bψ''
  have hnR:=compactWeightedMean_norm μ hψ hψ' x bψ'
  have hnF:=compactWeightedMean_norm μ hψ hF x bF
  have hnq:‖fderiv ℝ Q x‖≤B*(C+2*A*B)+(J+2*B*B)*A := by
    rw [hq.fderiv]
    exact (tensorDerivative_norm_le _ _ _ _).trans (add_le_add
      (mul_le_mul hnR hnf (norm_nonneg _) hB)
      (mul_le_mul hnr hnF (norm_nonneg _) (by positivity)))
  rw [heq]
  change ‖fderiv ℝ (compactWeightedMean μ ψ F'+compactWeightedMean μ ψ T-Q) x‖≤_
  rw [fderiv_sub ((hf' x).add (ht x)) hq.differentiableAt,
    fderiv_add (hf' x) (ht x)]
  calc
    _ ≤ ‖fderiv ℝ (compactWeightedMean μ ψ F') x+fderiv ℝ (compactWeightedMean μ ψ T) x‖+
        ‖fderiv ℝ Q x‖:=by
          convert norm_sub_le
            (fderiv ℝ (compactWeightedMean μ ψ F') x+fderiv ℝ (compactWeightedMean μ ψ T) x)
            (fderiv ℝ Q x) using 1
    _ ≤ (‖fderiv ℝ (compactWeightedMean μ ψ F') x‖+
        ‖fderiv ℝ (compactWeightedMean μ ψ T) x‖)+‖fderiv ℝ Q x‖:=
      by
        apply add_le_add _ le_rfl
        convert norm_add_le (fderiv ℝ (compactWeightedMean μ ψ F') x)
          (fderiv ℝ (compactWeightedMean μ ψ T) x) using 1
    _ ≤ (D+2*C*B)+(B*C+J*A+2*(B*A)*B)+(B*(C+2*A*B)+(J+2*B*B)*A):=
      add_le_add (add_le_add hnf' hnt) hnq
    _ = _:=by ring

end PersistencePays
#print axioms PersistencePays.compactWeightedMean_second_fderiv_norm
