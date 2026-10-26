import PersistencePays.GaussianTransportEntropy
import PersistencePays.WeakMomentConvergence

/-! Actual free-transport weak and entropy convergence. In particular, finite
Gaussian-reference entropy convergence forces convergence of each conditional
entropy; this follows from the chain rule and two lower semicontinuity bounds. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem transportProbability_weak_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hw : Tendsto μn atTop (𝓝 μ)) (t : ℝ) :
    Tendsto (fun n => transportProbability (μn n : Measure (E×E)) t) atTop
      (𝓝 (transportProbability (μ : Measure (E×E)) t)) :=
  (ProbabilityMeasure.continuous_map (show Continuous (freeTransport (E:=E) t) by
    unfold freeTransport drift; fun_prop)).continuousAt.tendsto.comp hw

theorem phase_quadratic_integral_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E×E))) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z,‖z‖^2 ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(μ : Measure (E×E)))))
    {f : E×E → ℝ} (hf : Continuous f) (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C*‖z‖^2) :
    Tendsto (fun n => ∫ z,f z ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,f z ∂(μ : Measure (E×E)))) := by
  apply weak_integral_tendsto_of_continuous_dominator hw hf
    (show Continuous (fun z : E×E => C*‖z‖^2) by fun_prop) hbound
    (fun n => (hμn n).integrable_norm_pow'.const_mul C) (hμ.integrable_norm_pow'.const_mul C)
  simpa only [integral_const_mul] using hm.const_mul C

theorem transportProbability_moment_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E×E))) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z,‖z‖^2 ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(μ : Measure (E×E))))) (t : ℝ) :
    Tendsto (fun n => ∫ z,‖z‖^2 ∂(transportProbability (μn n : Measure (E×E)) t : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(transportProbability (μ : Measure (E×E)) t : Measure (E×E)))) := by
  have he (ν : ProbabilityMeasure (E×E)) :
      (∫ z,‖z‖^2 ∂(transportProbability (ν : Measure (E×E)) t : Measure (E×E))) =
        ∫ z,‖freeTransport t z‖^2 ∂(ν : Measure (E×E)) :=
    integral_map (measurable_freeTransport t).aemeasurable (by fun_prop)
  simp_rw [he]
  apply phase_quadratic_integral_tendsto μn μ hμn hμ hw hm
    (by unfold freeTransport drift; fun_prop) ((1+|t|)^2)
  intro z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (freeTransport_norm_le t z)

theorem transported_position_moment_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E×E))) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z,‖z‖^2 ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(μ : Measure (E×E))))) (t : ℝ) :
    Tendsto (fun n => ∫ z,‖(freeTransport t z).1‖^2/2 ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,‖(freeTransport t z).1‖^2/2 ∂(μ : Measure (E×E)))) := by
  apply phase_quadratic_integral_tendsto μn μ hμn hμ hw hm
    (by unfold freeTransport drift; fun_prop) ((1+|t|)^2)
  intro z
  rw [Real.norm_of_nonneg (by positivity)]
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    ((norm_fst_le (freeTransport t z)).trans (freeTransport_norm_le t z))
  rw [mul_pow] at hh
  nlinarith [sq_nonneg ‖(freeTransport t z).1‖]

theorem gaussian_transport_entropy_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hμn : ∀ n, MemLp id 2 (μn n : Measure (E×E))) (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hKn : ∀ n, klDiv (μn n : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hm : Tendsto (fun n => ∫ z,‖z‖^2 ∂(μn n : Measure (E×E))) atTop
      (𝓝 (∫ z,‖z‖^2 ∂(μ : Measure (E×E)))))
    (hKe : Tendsto (fun n => (klDiv (μn n : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) atTop
      (𝓝 (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal)) (t : ℝ) :
    Tendsto (fun n => (klDiv (transportJoint (μn n : Measure (E×E)) t)
      (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) atTop
      (𝓝 (klDiv (transportJoint (μ : Measure (E×E)) t)
        (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) := by
  have hi (ν : ProbabilityMeasure (E×E)) (hν : MemLp id 2 (ν : Measure (E×E))) :
      (∫ z, (‖(freeTransport t z).1‖^2/2-‖z.1‖^2/2) ∂(ν : Measure (E×E))) =
        (∫ z,‖(freeTransport t z).1‖^2/2 ∂(ν : Measure (E×E)))-
          (∫ z,‖(freeTransport 0 z).1‖^2/2 ∂(ν : Measure (E×E))) := by
    have hit : Integrable (fun z : E×E => ‖(freeTransport t z).1‖^2/2) (ν : Measure (E×E)) :=
      (drift_memLp hν t).fst.integrable_norm_pow'.div_const 2
    have hi0 : Integrable (fun z : E×E => ‖z.1‖^2/2) (ν : Measure (E×E)) :=
      hν.fst.integrable_norm_pow'.div_const 2
    rw [integral_sub hit hi0]
    simp only [freeTransport,drift,zero_smul,add_zero]
  simp_rw [(gaussian_freeTransport_entropy _ (hμn _) (hKn _) t).2,
    (gaussian_freeTransport_entropy _ hμ hK t).2,hi _ (hμn _),hi _ hμ]
  exact hKe.add ((transported_position_moment_tendsto μn μ hμn hμ hw hm t).sub
    (transported_position_moment_tendsto μn μ hμn hμ hw hm 0))

end PersistencePays
#print axioms PersistencePays.gaussian_transport_entropy_tendsto
