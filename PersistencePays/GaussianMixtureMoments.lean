import PersistencePays.GaussianCovarianceOperator

/-! Mean and covariance of an actual independent Gaussian perturbation. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianMixture (ν:Measure E) (b:E) (τ:ℝ):Measure E :=
  (ν.prod (stdGaussian E)).map (fun q:E×E => b+q.1+τ•q.2)

instance gaussianMixture_probability (ν:Measure E) [IsProbabilityMeasure ν] (b:E) (τ:ℝ) :
    IsProbabilityMeasure (gaussianMixture ν b τ) := by
  unfold gaussianMixture
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma gaussianMixture_memLp (ν:Measure E) [IsProbabilityMeasure ν]
    (hν:MemLp id 2 ν) (b:E) (τ:ℝ) : MemLp id 2 (gaussianMixture ν b τ) := by
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable (by fun_prop)).mpr
  exact ((memLp_const b).add (hν.comp_fst _)).add
    (((IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)).comp_snd ν).const_smul τ)

lemma gaussianMixture_mean (ν:Measure E) [IsProbabilityMeasure ν]
    (hν:MemLp id 2 ν) (b:E) (τ:ℝ) :
    (∫ x,x ∂gaussianMixture ν b τ)=b+∫ x,x ∂ν := by
  have hγ:=IsGaussian.integrable_id (μ:=stdGaussian E)
  have hνi:=hν.integrable (by norm_num)
  have hi:Integrable (fun q:E×E => b+q.1+τ•q.2) (ν.prod (stdGaussian E)) :=
    ((integrable_const b).add (hνi.comp_fst _)).add ((hγ.comp_snd ν).smul τ)
  rw [gaussianMixture,integral_map (by fun_prop) (show AEStronglyMeasurable (fun x:E => x) _ from measurable_id.aestronglyMeasurable),
    integral_prod _ hi]
  have hinner (x:E):(∫ y:E,b+x+τ•y ∂stdGaussian E)=b+x := by
    have hiτ:Integrable (fun y:E => τ•y) (stdGaussian E):=hγ.smul τ
    rw [integral_add (integrable_const _) hiτ,integral_smul,integral_id_stdGaussian]
    simp
  change (∫ x,∫ y:E,b+x+τ•y ∂stdGaussian E ∂ν)=b+∫ x,x ∂ν
  simp_rw [hinner]
  rw [integral_add (integrable_const b) (show Integrable (fun x:E => x) ν from hνi)]
  simp

lemma covariance_fst_fst {ν η:Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (u v:E) :
    covariance (fun q:E×E => ⟪u,q.1⟫) (fun q:E×E => ⟪v,q.1⟫) (ν.prod η)=
      covariance (fun x:E => ⟪u,x⟫) (fun x:E => ⟪v,x⟫) ν := by
  rw [← covariance_map_fun (by fun_prop) (by fun_prop) measurable_fst.aemeasurable,
    Measure.map_fst_prod]
  simp

lemma covariance_snd_snd {ν η:Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (u v:E) :
    covariance (fun q:E×E => ⟪u,q.2⟫) (fun q:E×E => ⟪v,q.2⟫) (ν.prod η)=
      covariance (fun x:E => ⟪u,x⟫) (fun x:E => ⟪v,x⟫) η := by
  rw [← covariance_map_fun (by fun_prop) (by fun_prop) measurable_snd.aemeasurable,
    Measure.map_snd_prod]
  simp

lemma gaussianMixture_covariance_zero (ν:Measure E) [IsProbabilityMeasure ν]
    (hν:MemLp id 2 ν) (τ:ℝ) (u v:E) :
    covarianceBilin (gaussianMixture ν 0 τ) u v=
      covarianceBilin ν u v+τ^2*⟪u,v⟫ := by
  have hγ:=IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have hu:=inner_memLp_two ν hν u
  have hv:=inner_memLp_two ν hν v
  have hgu:=inner_memLp_two (stdGaussian E) hγ u
  have hgv:=inner_memLp_two (stdGaussian E) hγ v
  let X:E×E→ℝ := fun q => ⟪u,q.1⟫
  let Y:E×E→ℝ := fun q => τ*⟪u,q.2⟫
  let V:E×E→ℝ := fun q => ⟪v,q.1⟫
  let W:E×E→ℝ := fun q => τ*⟪v,q.2⟫
  have hX:MemLp X 2 (ν.prod (stdGaussian E)):=hu.comp_fst _
  have hY:MemLp Y 2 (ν.prod (stdGaussian E)):=(hgu.const_mul τ).comp_snd _
  have hV:MemLp V 2 (ν.prod (stdGaussian E)):=hv.comp_fst _
  have hW:MemLp W 2 (ν.prod (stdGaussian E)):=(hgv.const_mul τ).comp_snd _
  have hcross:covariance X W (ν.prod (stdGaussian E))=0 :=
    covariance_fst_snd_prod hu (hgv.const_mul τ)
  have hcross':covariance Y V (ν.prod (stdGaussian E))=0 := by
    rw [covariance_comm]
    exact covariance_fst_snd_prod hv (hgu.const_mul τ)
  rw [covarianceBilin_apply_eq_cov (gaussianMixture_memLp ν hν 0 τ)]
  unfold gaussianMixture
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [zero_add,inner_add_right,real_inner_smul_right]
  change covariance (X+Y) (V+W) _=_
  rw [covariance_add_left hX hY (hV.add hW),covariance_add_right hX hV hW,
    covariance_add_right hY hV hW,hcross,hcross',add_zero,zero_add]
  dsimp [X,V,Y,W]
  rw [covariance_fst_fst,covariance_const_mul_left,covariance_const_mul_right,
    covariance_snd_snd,← covarianceBilin_apply_eq_cov hν,← covarianceBilin_apply_eq_cov hγ,
    covarianceBilin_stdGaussian]
  change covarianceBilin ν u v+τ*(τ*⟪u,v⟫)=covarianceBilin ν u v+τ^2*⟪u,v⟫
  ring

lemma gaussianMixture_covariance (ν:Measure E) [IsProbabilityMeasure ν]
    (hν:MemLp id 2 ν) (b:E) (τ:ℝ) (u v:E) :
    covarianceBilin (gaussianMixture ν b τ) u v=
      covarianceBilin ν u v+τ^2*⟪u,v⟫ := by
  have he:gaussianMixture ν b τ=(gaussianMixture ν 0 τ).map (fun x => b+x) := by
    rw [gaussianMixture,gaussianMixture,Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext q
    simp only [Function.comp_apply,zero_add,add_assoc]
  haveI:IsProbabilityMeasure (gaussianMixture ν 0 τ):=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [he,covarianceBilin_map_const_add]
  exact gaussianMixture_covariance_zero ν hν τ u v

end
end PersistencePays
#print axioms PersistencePays.gaussianMixture_mean
#print axioms PersistencePays.gaussianMixture_covariance
