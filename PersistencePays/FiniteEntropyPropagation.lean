import PersistencePays.StartingEntropy
import PersistencePays.StepLaw
import PersistencePays.ComparisonVerlet

/-! Actual finite-entropy propagation through the numerical Gaussian/volume stages. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem noiseKernel_comp {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    (μ : Measure S) [SFinite μ] (ν : Measure B) [SFinite ν]
    (f : S × B → S) (hf : Measurable f) :
    FiniteNoise.noiseKernel ν f hf ∘ₘ μ = (μ.prod ν).map f := by
  rw [FiniteNoise.noiseKernel, ← Measure.map_comp _ _ hf,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

theorem phaseOUKernel_comp_map (μ : Measure (E × E)) [SFinite μ] (r σ : ℝ) :
    phaseOUKernel r σ ∘ₘ μ =
      (μ.prod (stdGaussian E)).map (fun p => OBABOPath.ou r σ p.2 p.1) := by
  have he : phaseOUKernel (E := E) r σ = FiniteNoise.noiseKernel (stdGaussian E)
      (fun p => OBABOPath.ou r σ p.2 p.1) (by unfold OBABOPath.ou; fun_prop) := by
    ext z : 1
    rw [phaseOUKernel_apply, FiniteNoise.noiseKernel_apply]
  rw [he, noiseKernel_comp]

theorem phaseOUKernel_memLp (μ : Measure (E × E)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : p ≠ ∞) (hμ : MemLp id p μ) (r σ : ℝ) :
    MemLp id p (phaseOUKernel r σ ∘ₘ μ) := by
  rw [phaseOUKernel_comp_map]
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (by unfold OBABOPath.ou; fun_prop)).mpr
  exact ou_memLp (hμ.comp_fst (stdGaussian E))
    ((IsGaussian.memLp_id (stdGaussian E) p hp).comp_snd μ) r σ

def verletEquiv (g : E → E) (hg : Measurable g) (h : ℝ) : (E × E) ≃ᵐ (E × E) where
  toFun := verlet g h
  invFun := verlet g (-h)
  left_inv := verlet_inverse g h
  right_inv := by intro z; simpa only [neg_neg] using verlet_inverse g (-h) z
  measurable_toFun := (verlet_measurePreserving g hg h).measurable
  measurable_invFun := (verlet_measurePreserving g hg (-h)).measurable

/-- A deterministic volume stage has finite relative entropy when its input
and output have finite quadratic moments. -/
theorem A1.volume_stage_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : (E × E) ≃ᵐ (E × E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (hμ : MemLp id 2 μ) (hμe : MemLp e 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    klDiv (μ.map e) (phaseGibbs U) ≠ ∞ := by
  rw [phaseGibbs_eq_tilted U a.twice_contDiff.continuous.measurable a.gibbs_integrable] at hK ⊢
  exact (volume_preserving_entropy_change _ (phaseEnergy U)
    (phaseEnergy_measurable U a.twice_contDiff.continuous.measurable)
    (phase_gibbs_integrable U a.gibbs_integrable) μ e he hK
      ((a.phaseEnergy_integrable hμe).sub (a.phaseEnergy_integrable hμ))).1

def gaussianSandwichKernel (D : E × E → E × E) (hD : Measurable D) (r σ : ℝ) :
    Kernel (E × E) (E × E) :=
  phaseOUKernel r σ ∘ₖ (Kernel.deterministic D hD ∘ₖ phaseOUKernel r σ)

instance gaussianSandwichKernel_markov (D : E × E → E × E) (hD : Measurable D) (r σ : ℝ) :
    IsMarkovKernel (gaussianSandwichKernel D hD r σ) := by
  unfold gaussianSandwichKernel
  infer_instance

theorem gaussianSandwichKernel_comp (μ : Measure (E × E)) [SFinite μ]
    (D : E × E → E × E) (hD : Measurable D) (r σ : ℝ) :
    gaussianSandwichKernel D hD r σ ∘ₘ μ =
      phaseOUKernel r σ ∘ₘ ((phaseOUKernel r σ ∘ₘ μ).map D) := by
  rw [gaussianSandwichKernel, ← Measure.comp_assoc, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

theorem A1.sandwich_entropy_finite {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (e : (E × E) ≃ᵐ (E × E))
    (he : MeasurePreserving e ((volume : Measure E).prod volume) ((volume : Measure E).prod volume))
    (r σ : ℝ) (hnorm : r^2+σ^2=1)
    (hμ : MemLp id 2 μ)
    (hemom : MemLp e 2 (phaseOUKernel r σ ∘ₘ μ))
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    klDiv (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) (phaseGibbs U) ≠ ∞ := by
  have hO := phaseOUKernel_invariant U r σ hnorm
  have hK₁ : klDiv (phaseOUKernel r σ ∘ₘ μ) (phaseGibbs U) ≠ ∞ :=
    ne_top_of_le_ne_top hK (klDiv_step_le _ _ _ hO)
  have hK₂ := a.volume_stage_entropy_finite (phaseOUKernel r σ ∘ₘ μ) e he
    (phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ) hemom hK₁
  rw [gaussianSandwichKernel_comp]
  exact ne_top_of_le_ne_top hK₂ (klDiv_step_le _ _ _ hO)


/-- The sandwich kernel uses exactly two independent standard Gaussian vectors. -/
theorem gaussianSandwichKernel_apply (D : E × E → E × E) (hD : Measurable D)
    (r σ : ℝ) (z : E × E) :
    gaussianSandwichKernel D hD r σ z =
      ((stdGaussian E).prod (stdGaussian E)).map
        (fun η => OBABOPath.ou r σ η.2 (D (OBABOPath.ou r σ η.1 z))) := by
  rw [gaussianSandwichKernel, ← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap]
  ext A hA
  rw [Kernel.comp_apply' _ _ _ hA, phaseOUKernel_apply]
  simp only [Kernel.comap_apply]
  rw [lintegral_map
    (f := fun b => phaseOUKernel r σ (D b) A)
    (g := fun ξ => OBABOPath.ou r σ ξ z)
    (((phaseOUKernel r σ).measurable_coe hA).comp hD)
    (by unfold OBABOPath.ou; fun_prop)]
  simp_rw [phaseOUKernel_apply]
  have hm : Measurable (fun η : E × E => OBABOPath.ou r σ η.2
      (D (OBABOPath.ou r σ η.1 z))) := by
    unfold OBABOPath.ou
    fun_prop
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  apply lintegral_congr
  intro ξ
  rw [Measure.map_apply (by unfold OBABOPath.ou; fun_prop) hA]
  rfl

theorem unadjustedStepKernel_eq_sandwich (g : E → E) (hg : Measurable g) (h r σ : ℝ) :
    OBABOPath.unadjustedStepKernel g hg h r σ =
      gaussianSandwichKernel (verlet g h) (verlet_measurePreserving g hg h).measurable r σ := by
  ext z : 1
  rw [OBABOPath.unadjustedStepKernel, FiniteNoise.noiseKernel_apply]
  let hD := (verlet_measurePreserving g hg h).measurable
  rw [gaussianSandwichKernel, ← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap]
  ext A hA
  rw [Kernel.comp_apply' _ _ _ hA, phaseOUKernel_apply]
  simp only [Kernel.comap_apply]
  rw [lintegral_map
    (f := fun b => phaseOUKernel r σ (verlet g h b) A)
    (g := fun ξ => OBABOPath.ou r σ ξ z)
    (((phaseOUKernel r σ).measurable_coe hA).comp hD)
    (by unfold OBABOPath.ou; fun_prop)]
  simp_rw [phaseOUKernel_apply]
  have hm : Measurable (fun η : E × E => OBABOPath.unadjustedStepWithNoise g h r σ (z,η)) :=
    (OBABOPath.measurable_unadjustedStepWithNoise g hg h r σ).comp
      (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  apply lintegral_congr
  intro ξ
  rw [Measure.map_apply (by unfold OBABOPath.ou; fun_prop) hA]
  rfl

theorem A1.unadjusted_entropy_step {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h r σ : ℝ) (hnorm : r^2+σ^2=1) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    klDiv (OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ ∘ₘ μ) (phaseGibbs U) ≠ ∞ := by
  rw [unadjustedStepKernel_eq_sandwich]
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  exact a.sandwich_entropy_finite μ (verletEquiv (gradient U) hg h)
    (verlet_measurePreserving (gradient U) hg h) r σ hnorm hμ
    (a.verlet_memLp (phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ) h) hK


theorem A1.unadjusted_step_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : p ≠ ∞) (hμ : MemLp id p μ) (h r σ : ℝ) :
    MemLp id p (OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ ∘ₘ μ) := by
  rw [unadjustedStepKernel_eq_sandwich, gaussianSandwichKernel_comp]
  apply phaseOUKernel_memLp _ p hp _ r σ
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (verlet_measurePreserving (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h).measurable.aemeasurable).mpr
  exact a.verlet_memLp (phaseOUKernel_memLp μ p hp hμ r σ) h

theorem A1.unadjusted_entropy_iterates {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h r σ : ℝ) (hnorm : r^2+σ^2=1) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) (n : ℕ) :
    let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
    MemLp id 2 (iterateKernel K n ∘ₘ μ) ∧
      klDiv (iterateKernel K n ∘ₘ μ) (phaseGibbs U) ≠ ∞ := by
  let K := OBABOPath.unadjustedStepKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ
  change MemLp id 2 (iterateKernel K n ∘ₘ μ) ∧ _
  induction n with
  | zero => simpa only [iterateKernel, Measure.id_comp] using And.intro hμ hK
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc]
    exact ⟨a.unadjusted_step_memLp _ 2 (by norm_num) ih.1 h r σ,
      a.unadjusted_entropy_step _ h r σ hnorm ih.1 ih.2⟩

/-- Every positive-time unadjusted law from a point mass has finite entropy.
No entropy assumption is imposed on the singular initial point mass. -/
theorem A1.unadjusted_cold_entropy {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (h r σ : ℝ) (hh : 0 < h) (hσ : 0 < σ) (hnorm : r^2+σ^2=1)
    (z : E × E) (n : ℕ) :
    klDiv (OBABOPath.unadjustedEpochKernel (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ (n+1) z) (phaseGibbs U) ≠ ∞ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let K := OBABOPath.unadjustedStepKernel (gradient U) hg h r σ
  induction n with
  | zero =>
    rw [OBABOPath.unadjustedEpochKernel_eq_iterate]
    simpa only [iterateKernel, Kernel.comp_id] using a.unadjusted_step_entropy_finite h r σ hh hσ z
  | succ n ih =>
    have hm := OBABOPath.unadjusted_kernel_finite_moments a h r σ (n+1) z 2 (by norm_num)
    rw [OBABOPath.unadjustedEpochKernel_eq_iterate] at ih hm ⊢
    change klDiv (K ∘ₘ (iterateKernel K (n+1) z)) (phaseGibbs U) ≠ ∞
    exact a.unadjusted_entropy_step _ h r σ hnorm hm ih

section ComparisonMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {p : ℝ≥0∞} {Z : Ω → E × E}

theorem velocityFlip_memLp (hZ : MemLp Z p μ) :
    MemLp (fun ω => velocityFlip (Z ω)) p μ := by
  apply MemLp.of_fst_snd
  exact ⟨hZ.fst, hZ.snd.neg⟩

theorem A1.comparisonVerlet_memLp {U : E → ℝ} {m L : ℝ}
    (a : A1 U m L) (hZ : MemLp Z p μ) (h vstar : ℝ) :
    MemLp (fun ω => comparisonVerlet (gradient U) h vstar (Z ω)) p μ := by
  have hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  have hm := (comparisonVerlet_measurePreserving (gradient U) hg h vstar).measurable
  have hv := a.verlet_memLp hZ h
  have hf := velocityFlip_memLp hZ
  apply (hv.norm.add hf.norm).of_le (hm.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable
  filter_upwards with ω
  dsimp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  unfold comparisonVerlet
  split_ifs
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

end ComparisonMoments

/-- The same finite-entropy conclusion applies to the actual comparison
Hamiltonian stage, including its velocity-flip branch. -/
theorem A1.comparison_entropy_step {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h vstar r σ : ℝ) (hnorm : r^2+σ^2=1) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    klDiv (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) (phaseGibbs U) ≠ ∞ := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  exact a.sandwich_entropy_finite μ (comparisonVerletEquiv (gradient U) hg h vstar)
    (comparisonVerlet_measurePreserving (gradient U) hg h vstar) r σ hnorm hμ
    (a.comparisonVerlet_memLp (phaseOUKernel_memLp μ 2 (by norm_num) hμ r σ) h vstar) hK


theorem A1.comparison_step_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : p ≠ ∞) (hμ : MemLp id p μ) (h vstar r σ : ℝ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    MemLp id p (gaussianSandwichKernel e e.measurable r σ ∘ₘ μ) := by
  dsimp only
  rw [gaussianSandwichKernel_comp]
  apply phaseOUKernel_memLp _ p hp _ r σ
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (comparisonVerletEquiv (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h vstar).measurable.aemeasurable).mpr
  exact a.comparisonVerlet_memLp (phaseOUKernel_memLp μ p hp hμ r σ) h vstar

/-- All finite moments propagate for every finite number of actual comparison
steps, including the nonsmooth cutoff and flip branch. -/
theorem A1.comparison_iterates_memLp {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp : p ≠ ∞) (hμ : MemLp id p μ) (h vstar r σ : ℝ) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let K := gaussianSandwichKernel e e.measurable r σ
    MemLp id p (iterateKernel K n ∘ₘ μ) := by
  dsimp only
  induction n with
  | zero => simpa only [iterateKernel, Measure.id_comp] using hμ
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc]
    exact a.comparison_step_memLp _ p hp ih h vstar r σ

theorem A1.comparison_entropy_iterates {U : E → ℝ} {m L : ℝ} (a : A1 U m L)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ]
    (h vstar r σ : ℝ) (hnorm : r^2+σ^2=1) (hμ : MemLp id 2 μ)
    (hK : klDiv μ (phaseGibbs U) ≠ ∞) (n : ℕ) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let e := comparisonVerletEquiv (gradient U) hg h vstar
    let K := gaussianSandwichKernel e e.measurable r σ
    klDiv (iterateKernel K n ∘ₘ μ) (phaseGibbs U) ≠ ∞ := by
  dsimp only
  induction n with
  | zero => simpa only [iterateKernel, Measure.id_comp] using hK
  | succ n ih =>
    rw [iterateKernel, ← Measure.comp_assoc]
    exact a.comparison_entropy_step _ h vstar r σ hnorm
      (a.comparison_iterates_memLp μ 2 (by norm_num) hμ h vstar r σ n) ih

end PersistencePays
#print axioms PersistencePays.A1.unadjusted_entropy_step

#print axioms PersistencePays.A1.unadjusted_cold_entropy
#print axioms PersistencePays.A1.comparison_entropy_step

#print axioms PersistencePays.A1.comparison_iterates_memLp
#print axioms PersistencePays.A1.comparison_entropy_iterates
