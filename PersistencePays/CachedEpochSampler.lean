import PersistencePays.CachedSamplerLaw
import PersistencePays.FiniteNoiseSchedule

/-! The canonical finite-array cached implementation with an arbitrary initial
law. This complements the existing fixed-start law and exact query count. -/
noncomputable section
namespace PersistencePays.CachedOBABO
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open OBABOPath

private theorem trajectory_eq_schedule {S B:Type*} (f:S×B→S) (N:ℕ) (z:S) (b:Fin N→B) :
    FiniteNoise.trajectory f N z b=FiniteNoise.scheduleTrajectory (fun _=>f) N z b := by
  induction N with
  | zero=>rfl
  | succ N ih=>simp only [FiniteNoise.trajectory,FiniteNoise.scheduleTrajectory,ih]

theorem simulate_random_start_law (U:E→ℝ) (hU:Measurable U) (g:E→E) (hg:Measurable g)
    (h r σ:ℝ) (steps N:ℕ) (ν:Measure (E×E)) [SFinite ν] :
    (ν.prod (Measure.pi (fun _:Fin N=>epochRandomness (E:=E) steps))).map
      (fun p=>(simulate U g h r σ steps N p.1 p.2).phase)=
      iterateKernel (epochKernel U hU g hg h r σ steps) N ∘ₘ ν := by
  simp_rw [simulate_phase_eq_trajectory,trajectory_eq_schedule]
  rw [FiniteNoise.scheduleTrajectory_random_start_law (epochRandomness (E:=E) steps) ν _
    (fun _=>measurable_epochEndpoint U hU g hg h r σ steps)]
  change evolve (fun _=>epochKernel U hU g hg h r σ steps) ν N=_
  induction N with
  | zero=>simp [evolve,iterateKernel]
  | succ N ih=>rw [evolve_succ,iterateKernel,←Measure.comp_assoc,ih]

end PersistencePays.CachedOBABO
#print axioms PersistencePays.CachedOBABO.simulate_random_start_law
