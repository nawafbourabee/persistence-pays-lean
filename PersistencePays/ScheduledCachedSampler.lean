import PersistencePays.GradientCost
import PersistencePays.FiniteNoiseSchedule
import PersistencePays.EpochLaw
import PersistencePays.StationaryFlow

/-! An arbitrary refresh schedule has a literal cached implementation,
with one new gradient per attempted step and the exact scheduled kernel law. -/
set_option maxHeartbeats 200000
noncomputable section
namespace PersistencePays.CachedOBABO
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scheduledAttempt (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : Bool) (b : (E×E)×ℝ) (s : State E) : State E :=
  attempt U g h r σ b.1.1 b.1.2 (if refresh then refreshThreshold s b.2 else s)

def scheduledWithNoise (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : Bool) (z : (E×E)×ℝ) (b : (E×E)×ℝ) : (E×E)×ℝ :=
  stepWithNoise U g h r σ (if refresh then (z.1,b.2) else z) b.1

theorem scheduledWithNoise_measurable (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : Bool) :
    Measurable (fun p : ((E×E)×ℝ) × ((E×E)×ℝ) => scheduledWithNoise U g h r σ refresh p.1 p.2) := by
  unfold scheduledWithNoise
  cases refresh <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact (OBABOPath.measurable_stepWithNoise_uncurry U hU g hg h r σ).comp
      (f := fun p : ((E×E)×ℝ) × ((E×E)×ℝ) => (p.1,p.2.1))
      (measurable_fst.prodMk measurable_snd.fst)
  · exact (OBABOPath.measurable_stepWithNoise_uncurry U hU g hg h r σ).comp
      (f := fun p : ((E×E)×ℝ) × ((E×E)×ℝ) => ((p.1.1,p.2.2),p.2.1))
      ((measurable_fst.fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

theorem scheduledAttempt_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : Bool) (b : (E×E)×ℝ) (s : State E) (hc : Consistent g s) :
    Consistent g (scheduledAttempt U g h r σ refresh b s) := by
  apply attempt_consistent
  cases refresh <;> exact hc

theorem scheduledAttempt_calls (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : Bool) (b : (E×E)×ℝ) (s : State E) :
    (scheduledAttempt U g h r σ refresh b s).calls = s.calls+1 := by
  unfold scheduledAttempt
  rw [attempt_calls]
  cases refresh <;> rfl

theorem attempt_projection_stepWithNoise (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (b : E×E) (s : State E) (hc : Consistent g s) :
    projection (attempt U g h r σ b.1 b.2 s) = stepWithNoise U g h r σ (projection s) b := by
  rw [stepWithNoise_eq_actualPath]
  have hh := runSteps_projection U g h r σ (fun _ => b.1) (fun _ => b.2) s hc 1
  exact hh

theorem scheduledAttempt_projection (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : Bool) (b : (E×E)×ℝ) (s : State E) (hc : Consistent g s) :
    projection (scheduledAttempt U g h r σ refresh b s) =
      scheduledWithNoise U g h r σ refresh (projection s) b := by
  unfold scheduledAttempt scheduledWithNoise
  cases refresh <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact attempt_projection_stepWithNoise U g h r σ b.1 s hc
  · exact attempt_projection_stepWithNoise U g h r σ b.1 (refreshThreshold s b.2) hc

def scheduledNoise : Measure ((E×E)×ℝ) :=
  ((stdGaussian E).prod (stdGaussian E)).prod (expMeasure 1)

instance scheduledNoise_probability : IsProbabilityMeasure (scheduledNoise (E:=E)) := by
  unfold scheduledNoise
  infer_instance

/-- Exact Gaussian/Exponential implementation of a scheduled attempted step. -/
theorem scheduledStepKernel_apply (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : Bool) (z : (E×E)×ℝ) :
    scheduledStepKernel U hU g hg h r σ refresh z =
      (scheduledNoise (E:=E)).map (scheduledWithNoise U g h r σ refresh z) := by
  have hm : Measurable (scheduledWithNoise U g h r σ refresh z) :=
    (scheduledWithNoise_measurable U hU g hg h r σ refresh).comp
      (f := fun b : (E×E)×ℝ => (z,b))
      (show Measurable (fun b : (E×E)×ℝ => (z,b)) from measurable_const.prodMk measurable_id)
  cases refresh
  · simp only [scheduledStepKernel, Bool.false_eq_true, ↓reduceIte]
    rw [stepKernel_apply]
    change _ = (scheduledNoise (E:=E)).map (stepWithNoise U g h r σ z ∘ Prod.fst)
    rw [← Measure.map_map (stepWithNoise_measurable U hU g hg h r σ z) measurable_fst]
    simp [scheduledNoise, Measure.map_fst_prod]
  · simp only [scheduledStepKernel, ↓reduceIte]
    ext A hA
    rw [Kernel.comp_apply' _ _ _ hA, thresholdRefreshKernel, Kernel.parallelComp_apply,
      Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
      lintegral_map (Kernel.measurable_coe _ hA) (by fun_prop)]
    rw [Measure.map_apply hm hA, scheduledNoise,
      Measure.prod_apply_symm (hm hA)]
    apply lintegral_congr
    intro ell
    rw [stepKernel_apply, Measure.map_apply (stepWithNoise_measurable U hU g hg h r σ _) hA]
    rfl

def runSchedule (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (b : ℕ → (E×E)×ℝ) (s : State E) : ℕ → State E
  | 0 => s
  | n+1 => scheduledAttempt U g h r σ (refresh n) (b n) (runSchedule U g h r σ refresh b s n)

theorem runSchedule_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (b : ℕ → (E×E)×ℝ) (s : State E)
    (hc : Consistent g s) (n : ℕ) : Consistent g (runSchedule U g h r σ refresh b s n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact scheduledAttempt_consistent U g h r σ (refresh n) (b n) _ ih

theorem runSchedule_calls (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (b : ℕ → (E×E)×ℝ) (s : State E) (n : ℕ) :
    (runSchedule U g h r σ refresh b s n).calls = s.calls+n := by
  induction n with
  | zero => simp [runSchedule]
  | succ n ih => rw [runSchedule, scheduledAttempt_calls, ih]; omega

/-- Every scheduled implementation pays exactly one initialization query and
one query per attempted step, including rejected proposals. -/
theorem scheduled_total_gradient_queries (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (b : ℕ → (E×E)×ℝ) (z : (E×E)×ℝ) (n : ℕ) :
    (runSchedule U g h r σ refresh b (initializeCache g z.1 z.2) n).calls = n+1 := by
  rw [runSchedule_calls, initialize_calls]
  omega


/-- Finite-array cached implementation, including the single initial gradient query. -/
def simulateSchedule (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) : (n : ℕ) → ((E×E)×ℝ) → (Fin n → (E×E)×ℝ) → State E
  | 0, z, _ => initializeCache g z.1 z.2
  | n+1, z, b => scheduledAttempt U g h r σ (refresh n) (b (Fin.last n))
      (simulateSchedule U g h r σ refresh n z (fun i => b i.castSucc))

theorem simulateSchedule_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (n : ℕ) (z : (E×E)×ℝ) (b : Fin n → (E×E)×ℝ) :
    Consistent g (simulateSchedule U g h r σ refresh n z b) := by
  induction n with
  | zero => exact initialize_consistent g z.1 z.2
  | succ n ih => exact scheduledAttempt_consistent U g h r σ (refresh n) (b (Fin.last n)) _ (ih _)

theorem simulateSchedule_queries (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (n : ℕ) (z : (E×E)×ℝ) (b : Fin n → (E×E)×ℝ) :
    (simulateSchedule U g h r σ refresh n z b).calls = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [simulateSchedule, scheduledAttempt_calls, ih]

theorem simulateSchedule_projection (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (refresh : ℕ → Bool) (n : ℕ) (z : (E×E)×ℝ) (b : Fin n → (E×E)×ℝ) :
    projection (simulateSchedule U g h r σ refresh n z b) =
      FiniteNoise.scheduleTrajectory
        (fun j p => scheduledWithNoise U g h r σ (refresh j) p.1 p.2) n z b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [simulateSchedule, scheduledAttempt_projection U g h r σ (refresh n) (b (Fin.last n)) _
        (simulateSchedule_consistent U g h r σ refresh n z _), ih]
      rfl

theorem scheduled_noiseKernel_eq (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : Bool) :
    FiniteNoise.noiseKernel (scheduledNoise (E:=E))
      (fun p => scheduledWithNoise U g h r σ refresh p.1 p.2)
      (scheduledWithNoise_measurable U hU g hg h r σ refresh) =
        scheduledStepKernel U hU g hg h r σ refresh := by
  ext z : 1
  rw [FiniteNoise.noiseKernel_apply, scheduledStepKernel_apply]

theorem simulateSchedule_law (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h r σ : ℝ) (refresh : ℕ → Bool)
    (ν : Measure ((E×E)×ℝ)) [SFinite ν] (n : ℕ) :
    (ν.prod (Measure.pi (fun _ : Fin n => scheduledNoise (E:=E)))).map
      (fun p => projection (simulateSchedule U g h r σ refresh n p.1 p.2)) =
      evolve (fun j => scheduledStepKernel U hU g hg h r σ (refresh j)) ν n := by
  simp_rw [simulateSchedule_projection]
  rw [FiniteNoise.scheduleTrajectory_random_start_law (scheduledNoise (E:=E)) ν _
    (fun j => scheduledWithNoise_measurable U hU g hg h r σ (refresh j))]
  congr 1
  funext j
  exact scheduled_noiseKernel_eq U hU g hg h r σ (refresh j)


end PersistencePays.CachedOBABO
#print axioms PersistencePays.CachedOBABO.scheduledStepKernel_apply
#print axioms PersistencePays.CachedOBABO.scheduled_total_gradient_queries

#print axioms PersistencePays.CachedOBABO.simulateSchedule_law
#print axioms PersistencePays.CachedOBABO.simulateSchedule_queries
