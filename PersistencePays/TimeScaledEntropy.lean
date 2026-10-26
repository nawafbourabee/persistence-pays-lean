import PersistencePays.NoOvershoot

/-! Free-transport no-overshoot on an arbitrary physical step interval. -/
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace PersistencePays
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def realScaleEquiv (h : ℝ) (hh : h ≠ 0) : E ≃L[ℝ] E where
  toFun := fun x => h • x
  invFun := fun x => h⁻¹ • x
  left_inv := by intro x; simp [smul_smul, hh]
  right_inv := by intro x; simp [smul_smul, hh]
  map_add' := by intro x y; simp [smul_add]
  map_smul' := by intro c x; simp [smul_smul, mul_comm]
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

def velocityScaleEquiv (h : ℝ) (hh : h ≠ 0) : (E × E) ≃ᵐ (E × E) where
  toFun := fun z => (z.1, h • z.2)
  invFun := fun z => (z.1, h⁻¹ • z.2)
  left_inv := by intro z; simp [smul_smul, hh]
  right_inv := by intro z; simp [smul_smul, hh]
  measurable_toFun := measurable_fst.prodMk (measurable_snd.const_smul h)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.const_smul h⁻¹)

lemma transportJoint_velocityScale (μ : Measure (E × E))
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    transportJoint (μ.map (velocityScaleEquiv h hh)) t =
      (transportJoint μ (h*t)).map (velocityScaleEquiv h hh) := by
  unfold transportJoint
  rw [Measure.map_map (measurable_freeTransport _) (velocityScaleEquiv h hh).measurable,
    Measure.map_map (velocityScaleEquiv h hh).measurable (measurable_freeTransport _)]
  congr 1
  funext z
  simp [Function.comp_def, velocityScaleEquiv, freeTransport, drift, smul_smul, mul_comm]

lemma transportPosition_velocityScale (μ : Measure (E × E))
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    transportPosition (μ.map (velocityScaleEquiv h hh)) t = transportPosition μ (h*t) := by
  unfold transportPosition
  rw [transportJoint_velocityScale]
  change (Measure.map (fun z : E × E => (z.1, h • z.2)) (transportJoint μ (h*t))).fst = _
  have hm : Measurable (fun z : E × E => h • z.2) := measurable_snd.const_smul h
  rw [Measure.fst_map_prodMk hm]
  rfl

lemma product_velocityScale (ν γ : Measure E) [SFinite ν] [SFinite γ]
    (h : ℝ) (hh : h ≠ 0) :
    ν.prod (γ.map (realScaleEquiv (E := E) h hh)) =
      (ν.prod γ).map (velocityScaleEquiv h hh) := by
  have hh' := Measure.map_prod_map ν γ measurable_id (realScaleEquiv h hh).continuous.measurable
  rw [Measure.map_id] at hh'
  exact hh'

lemma conditionalGaussianEntropy_velocityScale
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] (γ : Measure E) [IsProbabilityMeasure γ]
    (h : ℝ) (hh : h ≠ 0) (t : ℝ) :
    conditionalGaussianEntropy (μ.map (velocityScaleEquiv h hh))
      (γ.map (realScaleEquiv (E := E) h hh)) t = conditionalGaussianEntropy μ γ (h*t) := by
  unfold conditionalGaussianEntropy
  rw [transportJoint_velocityScale, transportPosition_velocityScale, product_velocityScale]
  exact klDiv_map_measurableEquiv (velocityScaleEquiv h hh)
    (transportJoint μ (h*t)) ((transportPosition μ (h*t)).prod γ)

/-- Corollary 3.5, with infinite endpoint entropies also allowed. -/
theorem corollary_3_5 (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    {h s : ℝ} (hh : 0 < h) (hs : 0 ≤ s) (hsh : s ≤ h) :
    conditionalGaussianEntropy μ (stdGaussian E) s ≤
      conditionalGaussianEntropy μ (stdGaussian E) 0 +
        conditionalGaussianEntropy μ (stdGaussian E) h := by
  have hne := ne_of_gt hh
  let μ' := μ.map (velocityScaleEquiv h hne)
  letI : IsProbabilityMeasure μ' :=
    Measure.isProbabilityMeasure_map (velocityScaleEquiv h hne).measurable.aemeasurable
  have hb := proposition_3_1_affine_law μ' (realScaleEquiv (E := E) h hne) 0
    (div_nonneg hs hh.le) ((div_le_one hh).mpr hsh)
  simp only [add_zero] at hb
  change conditionalGaussianEntropy (μ.map (velocityScaleEquiv h hne))
      ((stdGaussian E).map (realScaleEquiv h hne)) (s/h) ≤
    conditionalGaussianEntropy (μ.map (velocityScaleEquiv h hne))
      ((stdGaussian E).map (realScaleEquiv h hne)) 0 +
    conditionalGaussianEntropy (μ.map (velocityScaleEquiv h hne))
      ((stdGaussian E).map (realScaleEquiv h hne)) 1 at hb
  simp only [conditionalGaussianEntropy_velocityScale, mul_zero, mul_one] at hb
  have hc : h * (s/h) = s := by field_simp
  rwa [hc] at hb

/-- The integrated no-overshoot estimate, without any extra time-measurability
hypothesis: the nonnegative upper integral is bounded by pointwise domination. -/
theorem corollary_3_5_integrated (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) :
    (∫⁻ s in Set.Icc (0 : ℝ) h, conditionalGaussianEntropy μ (stdGaussian E) s) ≤
      ENNReal.ofReal h * (conditionalGaussianEntropy μ (stdGaussian E) 0 +
        conditionalGaussianEntropy μ (stdGaussian E) h) := by
  calc
    _ ≤ ∫⁻ _s in Set.Icc (0 : ℝ) h,
        (conditionalGaussianEntropy μ (stdGaussian E) 0 + conditionalGaussianEntropy μ (stdGaussian E) h) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact corollary_3_5 μ hh hs.1 hs.2
    _ = _ := by simp [lintegral_const, Real.volume_Icc, mul_comm]

end
end PersistencePays
#print axioms PersistencePays.corollary_3_5
#print axioms PersistencePays.corollary_3_5_integrated
