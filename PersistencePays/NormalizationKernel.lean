import PersistencePays.NormalizationSampler
import PersistencePays.CachedSamplerLaw

/-! Exact equality of original and normalized epoch laws, including all
reject/accept decisions and the literal cached implementation's oracle count. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory OBABOPath
open scoped ENNReal

lemma map_kernel_comp {S T:Type*} [MeasurableSpace S] [MeasurableSpace T]
    (K:Kernel S S) (K':Kernel T T) {f:S→T} (hf:Measurable f)
    (h:∀x,(K x).map f=K' (f x)) (μ:Measure S) :
    (K ∘ₘ μ).map f=K' ∘ₘ μ.map f := by
  ext A hA
  rw [Measure.map_apply hf hA,Measure.bind_apply (hf hA) K.aemeasurable,
    Measure.bind_apply hA K'.aemeasurable,
    lintegral_map (K'.measurable_coe hA) hf]
  apply lintegral_congr
  intro x
  rw [←h x,Measure.map_apply hf hA]

lemma map_evolve {S T:Type*} [MeasurableSpace S] [MeasurableSpace T]
    (K:Kernel S S) (K':Kernel T T) {f:S→T} (hf:Measurable f)
    (h:∀x,(K x).map f=K' (f x)) (μ:Measure S) (n:ℕ) :
    (evolve (fun _=>K) μ n).map f=evolve (fun _=>K') (μ.map f) n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [evolve_succ,evolve_succ,map_kernel_comp K K' hf h,ih]

lemma iterateKernel_comp_eq_evolve {S:Type*} [MeasurableSpace S]
    (K:Kernel S S) (μ:Measure S) (n:ℕ) :
    iterateKernel K n ∘ₘ μ=evolve (fun _=>K) μ n := by
  induction n with
  | zero=>exact Measure.id_comp
  | succ n ih=>rw [iterateKernel,←Measure.comp_assoc,ih,evolve_succ]

lemma trajectory_conjugate {S T B:Type*} (F:S→T)
    (f:S×B→S) (f':T×B→T) (hf:∀x b,f' (F x,b)=F (f (x,b)))
    (n:ℕ) (z:S) (b:Fin n→B) :
    FiniteNoise.trajectory f' n (F z) b=F (FiniteNoise.trajectory f n z b) := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [FiniteNoise.trajectory,ih,hf]

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma epochKernel_eq_noise_map (U:E→ℝ) (hU:Measurable U) (g:E→E) (hg:Measurable g)
    (h r σ:ℝ) (n:ℕ) (z:E×E) :
    epochKernel U hU g hg h r σ n z=
      (epochRandomness (E:=E) n).map (fun b=>epochEndpoint U g h r σ n (z,b)) := by
  ext A hA
  have hm:=measurable_epochEndpoint U hU g hg h r σ n
  have hz:Measurable (fun b:NoiseBlock E n×ℝ=>epochEndpoint U g h r σ n (z,b)):=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [epochKernel,Kernel.map_apply' _ hm _ hA,Kernel.id_prod_apply' _ _ (hm hA),
    Kernel.const_apply,Measure.map_apply hz hA]
  rfl

theorem A1.normalization_epochEndpoint {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (n:ℕ) (z:E×E) (b:NoiseBlock E n×ℝ) :
    epochEndpoint a.normalizedPotential (gradient a.normalizedPotential) (Real.sqrt m*h) r σ n
      (a.normalizationState z,b)=a.normalizationState (epochEndpoint U (gradient U) h r σ n (z,b)) := by
  exact congrArg Prod.fst (a.normalization_actualPath h r σ
    (fun k=>firstNoise n k b.1) (fun k=>secondNoise n k b.1) z b.2 n)

theorem A1.normalization_epochKernel {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (n:ℕ) (z:E×E) :
    (epochKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ n z).map a.normalizationState=
    epochKernel a.normalizedPotential a.normalizedPotential_A1.twice_contDiff.continuous.measurable
      (gradient a.normalizedPotential)
      (contDiff_gradient_of_twice_contDiff _ a.normalizedPotential_A1.twice_contDiff).continuous.measurable
      (Real.sqrt m*h) r σ n (a.normalizationState z) := by
  have hz:Measurable (fun b:NoiseBlock E n×ℝ=>epochEndpoint U (gradient U) h r σ n (z,b)):=
    (measurable_epochEndpoint _ a.twice_contDiff.continuous.measurable _
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable h r σ n).comp
      (measurable_const.prodMk measurable_id)
  rw [epochKernel_eq_noise_map,epochKernel_eq_noise_map,
    Measure.map_map a.normalizationState.measurable hz]
  congr 1
  funext b
  exact (a.normalization_epochEndpoint h r σ n z b).symm

theorem A1.normalization_epoch_laws {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (n N:ℕ) (ν:Measure (E×E)) :
    (evolve (fun _=>epochKernel U a.twice_contDiff.continuous.measurable (gradient U)
      (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
      h r σ n) ν N).map a.normalizationState=
    evolve (fun _=>epochKernel a.normalizedPotential
      a.normalizedPotential_A1.twice_contDiff.continuous.measurable
      (gradient a.normalizedPotential)
      (contDiff_gradient_of_twice_contDiff _ a.normalizedPotential_A1.twice_contDiff).continuous.measurable
      (Real.sqrt m*h) r σ n) (ν.map a.normalizationState) N :=
  map_evolve _ _ a.normalizationState.measurable (a.normalization_epochKernel h r σ n) ν N

theorem A1.normalization_simulate {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (n N:ℕ) (z:E×E) (b:Fin N→NoiseBlock E n×ℝ) :
    (CachedOBABO.simulate a.normalizedPotential (gradient a.normalizedPotential)
      (Real.sqrt m*h) r σ n N (a.normalizationState z) b).phase=
      a.normalizationState (CachedOBABO.simulate U (gradient U) h r σ n N z b).phase := by
  rw [CachedOBABO.simulate_phase_eq_trajectory,CachedOBABO.simulate_phase_eq_trajectory]
  exact trajectory_conjugate a.normalizationState _ _
    (a.normalization_epochEndpoint h r σ n) N z b

theorem A1.normalization_gradient_cost {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (n N:ℕ) (z:E×E) (b:Fin N→NoiseBlock E n×ℝ) :
    (CachedOBABO.simulate a.normalizedPotential (gradient a.normalizedPotential)
      (Real.sqrt m*h) r σ n N (a.normalizationState z) b).calls=
      (CachedOBABO.simulate U (gradient U) h r σ n N z b).calls ∧
    (CachedOBABO.simulate U (gradient U) h r σ n N z b).calls=N*n+1 := by
  simp only [CachedOBABO.simulate_queries_exact,and_self]

end PersistencePays
#print axioms PersistencePays.A1.normalization_epochKernel
#print axioms PersistencePays.A1.normalization_epoch_laws

#print axioms PersistencePays.A1.normalization_simulate
#print axioms PersistencePays.A1.normalization_gradient_cost
