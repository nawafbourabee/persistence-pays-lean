import PersistencePays.TruncationApproximation
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! An explicit transport coupling of a normalized restriction and its original
law. The discarded mass, including its quadratic moment, is charged exactly. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [MeasurableSpace S]

def truncationCoupling (μ : ProbabilityMeasure S) (A : Set S)
    (hpos : (μ : Measure S) A ≠ 0) : Measure (S × S) :=
  ((μ : Measure S).restrict A).map (fun x => (x,x)) +
    (conditionedProbability μ A hpos : Measure S).prod ((μ : Measure S).restrict Aᶜ)

theorem truncationCoupling_snd (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0) :
    (truncationCoupling μ A hpos).snd = (μ : Measure S) := by
  unfold truncationCoupling
  rw [Measure.snd_add]
  have hd : (Measure.map (fun x : S => (x,x)) ((μ : Measure S).restrict A)).snd =
      (μ : Measure S).restrict A := by
    change Measure.map Prod.snd (Measure.map (fun x : S => (x,x)) _) = _
    rw [Measure.map_map measurable_snd (show Measurable (fun x : S => (x,x)) from measurable_id.prodMk measurable_id)]
    exact Measure.map_id
  rw [hd]
  change _ + Measure.map Prod.snd _ = _
  rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.restrict_add_restrict_compl hA]

theorem truncationCoupling_fst (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0) :
    (truncationCoupling μ A hpos).fst = (conditionedProbability μ A hpos : Measure S) := by
  unfold truncationCoupling
  rw [Measure.fst_add]
  have hd : (Measure.map (fun x : S => (x,x)) ((μ : Measure S).restrict A)).fst =
      (μ : Measure S).restrict A := by
    change Measure.map Prod.fst (Measure.map (fun x : S => (x,x)) _) = _
    rw [Measure.map_map measurable_fst (show Measurable (fun x : S => (x,x)) from measurable_id.prodMk measurable_id)]
    exact Measure.map_id
  rw [hd]
  change _ + Measure.map Prod.fst _ = _
  rw [Measure.map_fst_prod, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hm : (μ : Measure S).restrict A =
      (μ : Measure S) A • (conditionedProbability μ A hpos : Measure S) := by
    rw [conditionedProbability_coe, ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel hpos (measure_ne_top _ _), one_smul]
  rw [hm, ← add_smul, measure_add_measure_compl hA, measure_univ, one_smul]

theorem truncationCoupling_probability (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0) :
    IsProbabilityMeasure (truncationCoupling μ A hpos) := by
  constructor
  rw [← Measure.snd_univ, truncationCoupling_snd μ A hA hpos, measure_univ]

def truncationPlan (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0) : ProbabilityMeasure (S × S) :=
  ⟨truncationCoupling μ A hpos,truncationCoupling_probability μ A hA hpos⟩

variable [NormedAddCommGroup S] [BorelSpace S] [PolishSpace S]

theorem truncationPlan_mem (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0) :
    truncationPlan μ A hA hpos ∈ QuadraticTransport.plans (conditionedProbability μ A hpos) μ := by
  constructor <;> apply Subtype.ext
  · exact truncationCoupling_fst μ A hA hpos
  · exact truncationCoupling_snd μ A hA hpos

theorem truncationPlan_cost_bound (μ : ProbabilityMeasure S) (A : Set S)
    (hA : MeasurableSet A) (hpos : (μ : Measure S) A ≠ 0)
    (hμ : MemLp id 2 (μ : Measure S)) :
    (QuadraticTransport.squaredCost (truncationPlan μ A hA hpos)).toReal ≤
      2*(((μ : Measure S) Aᶜ).toReal *
          (∫ x, ‖x‖^2 ∂(conditionedProbability μ A hpos : Measure S)) +
        (∫ x in Aᶜ, ‖x‖^2 ∂(μ : Measure S))) := by
  let P : Measure S := (conditionedProbability μ A hpos : Measure S)
  let Q : Measure S := (μ : Measure S).restrict Aᶜ
  have hp : MemLp id 2 P := memLp_conditionedProbability μ A hpos hμ
  have hq : MemLp id 2 Q := hμ.restrict _
  have hdiff : Integrable (fun z : S×S => ‖z.1-z.2‖^2) (P.prod Q) :=
    ((hp.comp_fst Q).sub (hq.comp_snd P)).norm.integrable_sq
  have hdiag : Integrable (fun z : S×S => ‖z.1-z.2‖^2)
      (((μ : Measure S).restrict A).map (fun x => (x,x))) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    change Integrable (fun x : S => ‖x-x‖^2) ((μ : Measure S).restrict A)
    simp
  have hi := QuadraticTransport.squaredCost_integrable _ _ _
    (truncationPlan_mem μ A hA hpos) hp.integrable_norm_pow' hμ.integrable_norm_pow'
  have hc : (QuadraticTransport.squaredCost (truncationPlan μ A hA hpos)).toReal =
      ∫ z : S×S, ‖z.1-z.2‖^2 ∂(P.prod Q) := by
    unfold QuadraticTransport.squaredCost
    rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z : S×S => sq_nonneg ‖z.1-z.2‖)) hi.aestronglyMeasurable]
    change (∫ z : S×S, ‖z.1-z.2‖^2 ∂(_ + P.prod Q)) = _
    rw [integral_add_measure hdiag hdiff, integral_map (by fun_prop) (by fun_prop)]
    simp
  rw [hc]
  have h1 : Integrable (fun z : S×S => ‖z.1‖^2) (P.prod Q) :=
    (hp.comp_fst Q).norm.integrable_sq
  have h2 : Integrable (fun z : S×S => ‖z.2‖^2) (P.prod Q) :=
    (hq.comp_snd P).norm.integrable_sq
  calc
    _ ≤ ∫ z : S×S, 2*(‖z.1‖^2+‖z.2‖^2) ∂(P.prod Q) := by
      apply integral_mono hdiff ((h1.add h2).const_mul 2)
      intro z
      change ‖z.1-z.2‖^2 ≤ 2*(‖z.1‖^2+‖z.2‖^2)
      have hh := norm_sub_le z.1 z.2
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
      nlinarith [sq_nonneg (‖z.1‖-‖z.2‖)]
    _ = _ := by
      rw [integral_const_mul, integral_add h1 h2, integral_fun_fst (fun x : S => ‖x‖^2), integral_fun_snd (fun x : S => ‖x‖^2)]
      have hPm : P.real univ = 1 := probReal_univ
      rw [hPm, one_smul]
      simp only [Q, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
      rfl

theorem conditioned_cost_tendsto (μ : ProbabilityMeasure S) (A : ℕ → Set S)
    (hA : ∀ n, MeasurableSet (A n)) (hpos : ∀ n, (μ : Measure S) (A n) ≠ 0)
    (hex : ∀ᵐ x ∂(μ : Measure S), ∀ᶠ n in atTop, x ∈ A n)
    (hμ : MemLp id 2 (μ : Measure S)) :
    Tendsto (fun n => (QuadraticTransport.cost (conditionedProbability μ (A n) (hpos n)) μ).toReal)
      atTop (𝓝 0) := by
  have hmass : Tendsto (fun n => ((μ : Measure S) (A n)ᶜ).toReal) atTop (𝓝 0) := by
    simp_rw [probability_complement_toReal (μ : Measure S) _ (hA _)]
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (exhausting_set_mass_tendsto μ A hA hex)
  have hm := conditioned_integral_tendsto μ A hA hpos hex hμ.integrable_norm_pow'
  have ht : Tendsto (fun n => ∫ x in (A n)ᶜ, ‖x‖^2 ∂(μ : Measure S)) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ x in (A n)ᶜ, ‖x‖^2 ∂(μ : Measure S)) =
        (∫ x, ‖x‖^2 ∂(μ : Measure S))-(∫ x in A n, ‖x‖^2 ∂(μ : Measure S)) := by
      have hh := integral_add_compl (hA n) hμ.integrable_norm_pow'
      simp only [id_eq] at hh
      linarith
    simp_rw [he]
    have hh : Tendsto (fun n => ∫ x in A n, ‖x‖^2 ∂(μ : Measure S)) atTop
        (𝓝 (∫ x, ‖x‖^2 ∂(μ : Measure S))) :=
      exhausting_set_integral_tendsto (μ : Measure S) A hA hex hμ.integrable_norm_pow'
    convert (tendsto_const_nhds (x := (∫ x, ‖x‖^2 ∂(μ : Measure S)))).sub hh using 1 <;> simp
  have hlim := ((hmass.mul hm).add ht).const_mul 2
  simp only [zero_mul,zero_add,mul_zero] at hlim
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hlim
  intro n
  have hcp := memLp_conditionedProbability μ (A n) (hpos n) hμ
  have hfin := QuadraticTransport.squaredCost_finite _ _ _
    (truncationPlan_mem μ (A n) (hA n) (hpos n)) hcp.integrable_norm_pow' hμ.integrable_norm_pow'
  exact (ENNReal.toReal_mono hfin (iInf₂_le _ (truncationPlan_mem μ (A n) (hA n) (hpos n)))).trans
    (truncationPlan_cost_bound μ (A n) (hA n) (hpos n) hμ)

end PersistencePays
#print axioms PersistencePays.truncationPlan_cost_bound
