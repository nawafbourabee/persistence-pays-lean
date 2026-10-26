import PersistencePays.TruncationApproximation

/-! A literal increasing sequence of bounded-support truncations with positive
normalizing masses for every index. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology
variable {S : Type*} [NormedAddCommGroup S] [MeasurableSpace S] [BorelSpace S]

theorem eventually_mem_closedBall_nat (x : S) :
    ∀ᶠ n : ℕ in atTop, x ∈ closedBall (0:S) n := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [mem_closedBall,dist_zero_right] using hN.trans (Nat.cast_le.mpr hn)

theorem exists_positive_ball (μ : ProbabilityMeasure S) :
    ∃ N : ℕ, (μ : Measure S) (closedBall (0:S) N) ≠ 0 := by
  have hh := exhausting_set_mass_tendsto μ (fun n : ℕ => closedBall (0:S) n)
    (fun _ => measurableSet_closedBall) (Filter.Eventually.of_forall eventually_mem_closedBall_nat)
  have he := hh.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N,hN⟩ := he.exists
  exact ⟨N,fun hz => by simp [hz] at hN⟩

def truncationRadiusOffset (μ : ProbabilityMeasure S) : ℕ := (exists_positive_ball μ).choose

def truncationBall (μ : ProbabilityMeasure S) (n : ℕ) : Set S :=
  closedBall 0 ((truncationRadiusOffset μ+n : ℕ):ℝ)

theorem truncationBall_measurable (μ : ProbabilityMeasure S) (n : ℕ) :
    MeasurableSet (truncationBall μ n) := measurableSet_closedBall

theorem truncationBall_mass_ne_zero (μ : ProbabilityMeasure S) (n : ℕ) :
    (μ : Measure S) (truncationBall μ n) ≠ 0 := by
  apply ne_of_gt
  apply lt_of_lt_of_le (pos_iff_ne_zero.mpr (exists_positive_ball μ).choose_spec)
  apply measure_mono
  apply closedBall_subset_closedBall
  exact_mod_cast Nat.le_add_right (truncationRadiusOffset μ) n

theorem truncationBall_exhausts (μ : ProbabilityMeasure S) (x : S) :
    ∀ᶠ n in atTop, x ∈ truncationBall μ n := by
  filter_upwards [eventually_mem_closedBall_nat x] with n hn
  exact closedBall_subset_closedBall (by exact_mod_cast Nat.le_add_left n (truncationRadiusOffset μ)) hn

def ballTruncation (μ : ProbabilityMeasure S) (n : ℕ) : ProbabilityMeasure S :=
  conditionedProbability μ (truncationBall μ n) (truncationBall_mass_ne_zero μ n)

theorem ballTruncation_tendsto (μ : ProbabilityMeasure S) :
    Tendsto (ballTruncation μ) atTop (𝓝 μ) :=
  conditionedProbability_tendsto μ (truncationBall μ) (truncationBall_measurable μ)
    (truncationBall_mass_ne_zero μ) (Filter.Eventually.of_forall (truncationBall_exhausts μ))

theorem ballTruncation_integral_tendsto (μ : ProbabilityMeasure S) {f : S → ℝ}
    (hf : Integrable f (μ : Measure S)) :
    Tendsto (fun n => ∫ x, f x ∂(ballTruncation μ n : Measure S)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure S))) :=
  conditioned_integral_tendsto μ (truncationBall μ) (truncationBall_measurable μ)
    (truncationBall_mass_ne_zero μ) (Filter.Eventually.of_forall (truncationBall_exhausts μ)) hf

theorem ballTruncation_ae_bounded (μ : ProbabilityMeasure S) (n : ℕ) :
    ∀ᵐ x ∂(ballTruncation μ n : Measure S), ‖x‖ ≤ truncationRadiusOffset μ+n := by
  have hh := ae_cond_mem (μ := (μ : Measure S)) (truncationBall_measurable μ n)
  change ∀ᵐ x ∂ProbabilityTheory.cond (μ : Measure S) (truncationBall μ n), _
  filter_upwards [hh] with x hx
  simpa only [truncationBall, mem_closedBall, dist_zero_right, Nat.cast_add] using hx

end PersistencePays
#print axioms PersistencePays.ballTruncation_tendsto
#print axioms PersistencePays.ballTruncation_ae_bounded
