import PersistencePays.MaximalCouplingKernel
import PersistencePays.MaximalCouplingMeasure

/-! A jointly measurable maximal coupling kernel, proved from its explicit densities. -/
noncomputable section
namespace PersistencePays.MaximalCoupling
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
  [MeasurableSpace.CountablyGenerated S]

theorem overlap_add_left_apply (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    overlapKernel K J a + leftKernel K J a = K a := by
  exact congrArg (fun H : Kernel A S => H a) (overlap_add_left K J)

theorem overlap_add_right_apply (K J : Kernel A S) [IsFiniteKernel K] [IsFiniteKernel J] (a : A) :
    overlapKernel K J a + rightKernel K J a = J a := by
  exact congrArg (fun H : Kernel A S => H a) (overlap_add_right K J)

instance maximalKernel_markov (K J : Kernel A S) [IsMarkovKernel K] [IsMarkovKernel J] :
    IsMarkovKernel (maximalKernel K J) := by
  constructor
  intro a
  rw [maximalKernel_apply]
  exact residualCoupling_isProbabilityMeasure (K a) (J a)
    (overlapKernel K J a) (leftKernel K J a) (rightKernel K J a)
    (overlap_add_left_apply K J a) (overlap_add_right_apply K J a)

theorem maximalKernel_fst (K J : Kernel A S) [IsMarkovKernel K] [IsMarkovKernel J] :
    (maximalKernel K J).fst = K := by
  ext a : 1
  rw [Kernel.fst_apply, maximalKernel_apply]
  change (residualCoupling (overlapKernel K J a) (leftKernel K J a) (rightKernel K J a)).fst = _
  rw [residualCoupling_fst _ _ _ (residual_mass_eq (K a) (J a) _ _ _
    (overlap_add_left_apply K J a) (overlap_add_right_apply K J a)), overlap_add_left_apply]

theorem maximalKernel_snd (K J : Kernel A S) [IsMarkovKernel K] [IsMarkovKernel J] :
    (maximalKernel K J).snd = J := by
  ext a : 1
  rw [Kernel.snd_apply, maximalKernel_apply]
  change (residualCoupling (overlapKernel K J a) (leftKernel K J a) (rightKernel K J a)).snd = _
  rw [residualCoupling_snd _ _ _ (residual_mass_eq (K a) (J a) _ _ _
    (overlap_add_left_apply K J a) (overlap_add_right_apply K J a)), overlap_add_right_apply]

theorem maximalKernel_disagreement (K J : Kernel A S) [IsMarkovKernel K] [IsMarkovKernel J]
    (hd : MeasurableSet {z : S×S | z.1 ≠ z.2}) (a : A) :
    maximalKernel K J a {z | z.1 ≠ z.2} = probabilityTV (K a) (J a) := by
  rw [maximalKernel_apply]
  exact (residualCoupling_maximal (K a) (J a)
    (overlapKernel K J a) (leftKernel K J a) (rightKernel K J a)
    (overlap_add_left_apply K J a) (overlap_add_right_apply K J a)
    (positiveResidualSet K J a) (positiveResidualSet_measurable K J a)
    (leftKernel_supported K J a) (rightKernel_supported K J a) hd).2.2

end PersistencePays.MaximalCoupling
#print axioms PersistencePays.MaximalCoupling.maximalKernel_disagreement
