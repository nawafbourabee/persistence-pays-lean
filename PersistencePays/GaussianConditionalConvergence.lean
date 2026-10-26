import PersistencePays.TransportApproximation
import PersistencePays.TrapezoidEntropy

/-! Conditional entropy converges along actual entropy-convergent Gaussian
regularizations, both pointwise in time and in time integrals. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem conditionalKL_toReal_eventually_gt
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hw : Tendsto μn atTop (𝓝 μ))
    (hKn : ∀ n, klDiv (μn n : Measure (E×E)) ((μn n : Measure (E×E)).fst.prod (stdGaussian E)) ≠ ∞)
    (hK : klDiv (μ : Measure (E×E)) ((μ : Measure (E×E)).fst.prod (stdGaussian E)) ≠ ∞)
    {b : ℝ} (hb : b < (klDiv (μ : Measure (E×E)) ((μ : Measure (E×E)).fst.prod (stdGaussian E))).toReal) :
    ∀ᶠ n in atTop, b < (klDiv (μn n : Measure (E×E))
      ((μn n : Measure (E×E)).fst.prod (stdGaussian E))).toReal := by
  by_cases hb0 : 0 ≤ b
  · have he := hw.eventually
      ((conditionalKL_lowerSemicontinuous (⟨stdGaussian E,inferInstance⟩ : ProbabilityMeasure E) μ)
        (ENNReal.ofReal b) ((ENNReal.ofReal_lt_iff_lt_toReal hb0 hK).mpr hb))
    exact he.mono (fun n hn => (ENNReal.ofReal_lt_iff_lt_toReal hb0 (hKn n)).mp hn)
  · exact Filter.Eventually.of_forall (fun n => (lt_of_not_ge hb0).trans_le ENNReal.toReal_nonneg)

theorem gaussian_conditional_entropy_tendsto
    (μn : ℕ → ProbabilityMeasure (E×E)) (μ : ProbabilityMeasure (E×E))
    (hKn : ∀ n, klDiv (μn n : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hw : Tendsto μn atTop (𝓝 μ))
    (hKe : Tendsto (fun n => (klDiv (μn n : Measure (E×E))
      (gaussianPairProbability (E:=E) : Measure (E×E))).toReal) atTop
      (𝓝 (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal)) :
    Tendsto (fun n => (conditionalGaussianEntropy (μn n : Measure (E×E)) (stdGaussian E) 0).toReal) atTop
      (𝓝 (conditionalGaussianEntropy (μ : Measure (E×E)) (stdGaussian E) 0).toReal) := by
  have hfin (ν : ProbabilityMeasure (E×E))
      (hk : klDiv (ν : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) :
      klDiv (ν : Measure (E×E)).fst (stdGaussian E) ≠ ∞ ∧
      klDiv (ν : Measure (E×E)) ((ν : Measure (E×E)).fst.prod (stdGaussian E)) ≠ ∞ := by
    have he := klDiv_product_reference_decomposition (ν : Measure (E×E)) (stdGaussian E) (stdGaussian E)
    change klDiv (ν : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) = _ at he
    constructor
    · apply ne_top_of_le_ne_top hk
      rw [he]
      exact le_add_right le_rfl
    · apply ne_top_of_le_ne_top hk
      rw [he]
      exact le_add_left le_rfl
  have heq (ν : ProbabilityMeasure (E×E))
      (hk : klDiv (ν : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) :
      (klDiv (ν : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal =
        (klDiv (ν : Measure (E×E)).fst (stdGaussian E)).toReal +
        (klDiv (ν : Measure (E×E)) ((ν : Measure (E×E)).fst.prod (stdGaussian E))).toReal := by
    change (klDiv (ν : Measure (E×E)) ((stdGaussian E).prod (stdGaussian E))).toReal = _
    rw [klDiv_product_reference_decomposition,ENNReal.toReal_add (hfin ν hk).1 (hfin ν hk).2]
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero]
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact conditionalKL_toReal_eventually_gt μn μ hw (fun n => (hfin _ (hKn n)).2) (hfin _ hK).2 hb
  · intro b hb
    let δ := (b-(klDiv (μ : Measure (E×E)) ((μ : Measure (E×E)).fst.prod (stdGaussian E))).toReal)/3
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have ht := hKe.eventually (gt_mem_nhds (show
      (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal <
        (klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E))).toReal+δ by linarith))
    have hp := klDiv_toReal_eventually_gt
      (fun n => (μn n).map measurable_fst.aemeasurable) (μ.map measurable_fst.aemeasurable)
      (⟨stdGaussian E,inferInstance⟩ : ProbabilityMeasure E)
      ((ProbabilityMeasure.continuous_map continuous_fst).continuousAt.tendsto.comp hw)
      (fun n => (hfin _ (hKn n)).1) (hfin _ hK).1
      (b := (klDiv (μ : Measure (E×E)).fst (stdGaussian E)).toReal-δ) (by
        change (klDiv (μ : Measure (E×E)).fst (stdGaussian E)).toReal-δ <
          (klDiv (μ : Measure (E×E)).fst (stdGaussian E)).toReal
        linarith)
    filter_upwards [ht,hp] with n hn hnP
    have hi := heq (μn n) (hKn n)
    have hl := heq μ hK
    change (klDiv (μ : Measure (E×E)).fst (stdGaussian E)).toReal-δ <
      (klDiv (μn n : Measure (E×E)).fst (stdGaussian E)).toReal at hnP
    dsimp [δ] at hn hnP
    linarith

theorem regularizedGaussian_conditional_entropy_tendsto
    (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => (conditionalGaussianEntropy
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) (stdGaussian E) t).toReal) atTop
      (𝓝 (conditionalGaussianEntropy (μ : Measure (E×E)) (stdGaussian E) t).toReal) := by
  let μn := regularizedProbability μ gaussianPairProbability ε
  have hn (n : ℕ) : MemLp id 2 (μn n : Measure (E×E)) :=
    regularizedProbability_memLp μ gaussianPairProbability ε hμ (gaussianPair_memLp 2 (by norm_num)) n
  have hKn := regularizedGaussian_entropy_finite μ ε hμ hK
  have hw := regularizedProbability_weak μ gaussianPairProbability ε hε
  have hm := regularizedProbability_moment μ gaussianPairProbability ε hμ
    (gaussianPair_memLp 2 (by norm_num)) hε
  have he := gaussian_conditional_entropy_tendsto
    (fun n => transportProbability (μn n : Measure (E×E)) t) (transportProbability (μ : Measure (E×E)) t)
    (fun n => (gaussian_freeTransport_entropy _ (hn n) (hKn n) t).1)
    (gaussian_freeTransport_entropy _ hμ hK t).1
    (transportProbability_weak_tendsto μn μ hw t)
    (gaussian_transport_entropy_tendsto μn μ hn hμ hKn hK hw hm
      (regularizedGaussian_entropy_tendsto μ ε hμ hK hε) t)
  simp only [conditionalGaussianEntropy,transportJoint_zero,transportPosition_zero] at he ⊢
  convert he using 1 <;> rfl


/-- The actual conditional-entropy time integrals converge. The domination is
obtained from the proved no-overshoot theorem and convergent endpoint entropies. -/
theorem regularizedGaussian_conditional_integral_tendsto
    (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => ∫ s in (0:ℝ)..h, (conditionalGaussianEntropy
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) (stdGaussian E) s).toReal) atTop
      (𝓝 (∫ s in (0:ℝ)..h, (conditionalGaussianEntropy (μ : Measure (E×E)) (stdGaussian E) s).toReal)) := by
  let μn := regularizedProbability μ gaussianPairProbability ε
  have hn (n : ℕ) : MemLp id 2 (μn n : Measure (E×E)) :=
    regularizedProbability_memLp μ gaussianPairProbability ε hμ (gaussianPair_memLp 2 (by norm_num)) n
  have hKn := regularizedGaussian_entropy_finite μ ε hμ hK
  have hfin (n : ℕ) (s : ℝ) : conditionalGaussianEntropy (μn n : Measure (E×E)) (stdGaussian E) s ≠ ∞ :=
    (gaussian_conditional_boltzmann_identity _ (hn n) (hKn n) s).1
  let b : ℕ → ℝ := fun n => (conditionalGaussianEntropy (μn n : Measure (E×E)) (stdGaussian E) 0).toReal+
    (conditionalGaussianEntropy (μn n : Measure (E×E)) (stdGaussian E) h).toReal
  have hb := (regularizedGaussian_conditional_entropy_tendsto μ ε hμ hK hε 0).add
    (regularizedGaussian_conditional_entropy_tendsto μ ε hμ hK hε h)
  obtain ⟨C,hC,hbound⟩ := (Metric.isBounded_range_of_tendsto b hb).exists_pos_norm_le
  simp_rw [intervalIntegral.integral_of_le hh.le]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => C)
    (fun n => (measurable_conditionalGaussianEntropy (μn n : Measure (E×E))
      (stdGaussian E)).ennreal_toReal.aestronglyMeasurable.restrict) (integrable_const _)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin n 0,hfin n h⟩)
      (corollary_3_5 (μn n : Measure (E×E)) hh hs.1.le hs.2)
    rw [ENNReal.toReal_add (hfin n 0) (hfin n h)] at he
    exact he.trans ((le_abs_self (b n)).trans (by
      simpa only [Real.norm_eq_abs] using hbound (b n) (mem_range_self n)))
  · exact Filter.Eventually.of_forall (fun s => regularizedGaussian_conditional_entropy_tendsto μ ε hμ hK hε s)


theorem regularizedGaussian_boltzmann_tendsto
    (μ : ProbabilityMeasure (E×E)) (ε : ℕ → ℝ)
    (hμ : MemLp id 2 (μ : Measure (E×E)))
    (hK : klDiv (μ : Measure (E×E)) (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞)
    (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => boltzmannEntropy (transportPosition
      (regularizedProbability μ gaussianPairProbability ε n : Measure (E×E)) t)) atTop
      (𝓝 (boltzmannEntropy (transportPosition (μ : Measure (E×E)) t))) := by
  let μn := regularizedProbability μ gaussianPairProbability ε
  have hn (n : ℕ) : MemLp id 2 (μn n : Measure (E×E)) :=
    regularizedProbability_memLp μ gaussianPairProbability ε hμ (gaussianPair_memLp 2 (by norm_num)) n
  have hKn := regularizedGaussian_entropy_finite μ ε hμ hK
  have hw := regularizedProbability_weak μ gaussianPairProbability ε hε
  have hm := regularizedProbability_moment μ gaussianPairProbability ε hμ
    (gaussianPair_memLp 2 (by norm_num)) hε
  have heq (ν : Measure (E×E)) [IsProbabilityMeasure ν] (hν : MemLp id 2 ν)
      (hk : klDiv ν (gaussianPairProbability (E:=E) : Measure (E×E)) ≠ ∞) :
      boltzmannEntropy (transportPosition ν t) =
        (klDiv ν (gaussianPairProbability (E:=E) : Measure (E×E))).toReal -
          (∫ z,‖(freeTransport 0 z).1‖^2/2 ∂ν) -
          (Module.finrank ℝ E:ℝ)/2*Real.log (2*Real.pi) -
          (conditionalGaussianEntropy ν (stdGaussian E) t).toReal := by
    have hh := (gaussian_conditional_boltzmann_identity ν hν hk t).2.2
    simp only [freeTransport,drift,zero_smul,add_zero]
    linarith
  change Tendsto (fun n => boltzmannEntropy (transportPosition (μn n : Measure (E×E)) t)) atTop _
  simp_rw [heq _ (hn _) (hKn _),heq _ hμ hK]
  exact (((regularizedGaussian_entropy_tendsto μ ε hμ hK hε).sub
    (transported_position_moment_tendsto μn μ hn hμ hw hm 0)).sub_const _).sub
    (regularizedGaussian_conditional_entropy_tendsto μ ε hμ hK hε t)

end PersistencePays
#print axioms PersistencePays.regularizedGaussian_conditional_entropy_tendsto

#print axioms PersistencePays.regularizedGaussian_conditional_integral_tendsto

#print axioms PersistencePays.regularizedGaussian_boltzmann_tendsto
