import PersistencePays.AdditiveNoiseApproximation

/-! A literal coupling transports the old coupling and adds independent noise
only to its first marginal. This avoids assuming Wasserstein convergence. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [PolishSpace S]

def noisyTransportPlan (π : ProbabilityMeasure (S×S)) (γ : ProbabilityMeasure S) (ε : ℝ) :
    ProbabilityMeasure (S×S) :=
  (π.prod γ).map (show Measurable (fun z : (S×S)×S => (z.1.1+ε•z.2,z.1.2)) by fun_prop).aemeasurable

theorem noisyTransportPlan_mem (μ ν γ : ProbabilityMeasure S)
    (π : ProbabilityMeasure (S×S)) (hπ : π ∈ QuadraticTransport.plans μ ν) (ε : ℝ) :
    noisyTransportPlan π γ ε ∈ QuadraticTransport.plans (additiveNoiseProbability μ γ ε) ν := by
  have hf : (π : Measure (S×S)).map Prod.fst = (μ : Measure S) :=
    congrArg (fun q : ProbabilityMeasure S => (q : Measure S)) hπ.1
  have hs : (π : Measure (S×S)).map Prod.snd = (ν : Measure S) :=
    congrArg (fun q : ProbabilityMeasure S => (q : Measure S)) hπ.2
  constructor
  · apply Subtype.ext
    change (((π : Measure (S×S)).prod (γ : Measure S)).map
      (fun z : (S×S)×S => (z.1.1+ε•z.2,z.1.2))).map Prod.fst =
        ((μ : Measure S).prod (γ : Measure S)).map (fun z : S×S => z.1+ε•z.2)
    rw [Measure.map_map measurable_fst (by fun_prop), ← hf,
      ← Measure.map_id (μ := (γ : Measure S)), Measure.map_prod_map (π : Measure (S×S)) (γ : Measure S) measurable_fst measurable_id,
      Measure.map_map (by fun_prop) (measurable_fst.prodMap measurable_id), Measure.map_id]
    rfl
  · apply Subtype.ext
    change (((π : Measure (S×S)).prod (γ : Measure S)).map
      (fun z : (S×S)×S => (z.1.1+ε•z.2,z.1.2))).map Prod.snd = (ν : Measure S)
    rw [Measure.map_map measurable_snd (by fun_prop)]
    calc
      _ = (((π : Measure (S×S)).prod (γ : Measure S)).map Prod.fst).map Prod.snd := by
        rw [Measure.map_map measurable_snd measurable_fst]
        rfl
      _ = _ := by rw [Measure.map_fst_prod,measure_univ,one_smul,hs]

theorem noisyTransportPlan_cost_bound (μ ν γ : ProbabilityMeasure S)
    (π : ProbabilityMeasure (S×S)) (hπ : π ∈ QuadraticTransport.plans μ ν) (ε : ℝ)
    (hμ : MemLp id 2 (μ : Measure S)) (hν : MemLp id 2 (ν : Measure S))
    (hγ : MemLp id 2 (γ : Measure S)) :
    (QuadraticTransport.squaredCost (noisyTransportPlan π γ ε)).toReal ≤
      2*(QuadraticTransport.squaredCost π).toReal+2*ε^2*(∫ x, ‖x‖^2 ∂(γ : Measure S)) := by
  have hbase := QuadraticTransport.squaredCost_integrable μ ν π hπ
    hμ.integrable_norm_pow' hν.integrable_norm_pow'
  have hnew := QuadraticTransport.squaredCost_integrable _ _ _
    (noisyTransportPlan_mem μ ν γ π hπ ε)
    (additiveNoiseProbability_memLp μ γ ε hμ hγ).integrable_norm_pow' hν.integrable_norm_pow'
  have h1 : Integrable (fun z : (S×S)×S => ‖z.1.1-z.1.2‖^2)
      ((π : Measure (S×S)).prod (γ : Measure S)) := hbase.comp_fst (γ : Measure S)
  have h2 : Integrable (fun z : (S×S)×S => ‖z.2‖^2)
      ((π : Measure (S×S)).prod (γ : Measure S)) := hγ.integrable_norm_pow'.comp_snd (π : Measure (S×S))
  have hnew' : Integrable (fun z : (S×S)×S => ‖z.1.1+ε•z.2-z.1.2‖^2)
      ((π : Measure (S×S)).prod (γ : Measure S)) := by
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).mp hnew
  have he0 : (QuadraticTransport.squaredCost π).toReal =
      ∫ z : S×S, ‖z.1-z.2‖^2 ∂(π : Measure (S×S)) :=
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      hbase.aestronglyMeasurable).symm
  have he1 : (QuadraticTransport.squaredCost (noisyTransportPlan π γ ε)).toReal =
      ∫ z : (S×S)×S, ‖z.1.1+ε•z.2-z.1.2‖^2 ∂((π : Measure (S×S)).prod (γ : Measure S)) := by
    unfold QuadraticTransport.squaredCost
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun z : S×S => sq_nonneg ‖z.1-z.2‖)) hnew.aestronglyMeasurable]
    exact integral_map (by fun_prop) (by fun_prop)
  rw [he0,he1]
  calc
    _ ≤ ∫ z : (S×S)×S, 2*‖z.1.1-z.1.2‖^2+2*ε^2*‖z.2‖^2
        ∂((π : Measure (S×S)).prod (γ : Measure S)) := by
      apply integral_mono hnew' ((h1.const_mul 2).add (h2.const_mul _))
      intro z
      change ‖z.1.1+ε•z.2-z.1.2‖^2 ≤ 2*‖z.1.1-z.1.2‖^2+2*ε^2*‖z.2‖^2
      have hn : ‖z.1.1+ε•z.2-z.1.2‖ ≤ ‖z.1.1-z.1.2‖+|ε| *‖z.2‖ := by
        simpa only [show z.1.1+ε•z.2-z.1.2 = (z.1.1-z.1.2)+ε•z.2 by abel,
          norm_smul,Real.norm_eq_abs] using norm_add_le (z.1.1-z.1.2) (ε•z.2)
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
      nlinarith [sq_abs ε, sq_nonneg (‖z.1.1-z.1.2‖-|ε| *‖z.2‖)]
    _ = _ := by
      rw [integral_add (h1.const_mul 2) (h2.const_mul _), integral_const_mul, integral_const_mul,
        integral_fun_fst (fun z : S×S => ‖z.1-z.2‖^2), integral_fun_snd (fun z : S => ‖z‖^2),
        probReal_univ,one_smul,probReal_univ,one_smul]

end PersistencePays
#print axioms PersistencePays.noisyTransportPlan_cost_bound
