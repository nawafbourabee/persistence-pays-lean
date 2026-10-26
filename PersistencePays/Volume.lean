import PersistencePays.Threshold
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue preservation of the actual Verlet map

The proof uses translation-invariant product measure and the three shears,
so it includes nonsmooth measurable forces. The shear construction follows
the checked construction in the local `CoupledJacobi/VerletVolume.lean`
project, restated here for this paper's literal `kick`, `drift`, and `verlet`.
Only mathlib and this project's proved modules are imported.
-/

noncomputable section
namespace PersistencePays
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem kick_measurePreserving (g : E → E) (hg : Measurable g) (t : ℝ) :
    MeasurePreserving (kick g t) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := by
  exact (MeasurePreserving.id (volume : Measure E)).skew_product
    (measurable_snd.sub ((hg.comp measurable_fst).const_smul t))
    (ae_of_all _ (fun x => (measurePreserving_sub_right (volume : Measure E) (t • g x)).map_eq))

theorem drift_measurePreserving (t : ℝ) :
    MeasurePreserving (drift (E := E) t) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := by
  have hs : MeasurePreserving (Prod.swap : E × E → E × E)
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
    Measure.measurePreserving_swap
  have ht : MeasurePreserving (fun z : E × E => (z.1, z.2 + t • z.1))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
    (MeasurePreserving.id (volume : Measure E)).skew_product
      (measurable_snd.add (measurable_fst.const_smul t))
      (ae_of_all _ (fun x => (measurePreserving_add_right (volume : Measure E) (t • x)).map_eq))
  exact hs.comp (ht.comp hs)

theorem verlet_measurePreserving (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (verlet g h) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) :=
  (kick_measurePreserving g hg (h / 2)).comp
    ((drift_measurePreserving h).comp (kick_measurePreserving g hg (h / 2)))

theorem velocityFlip_measurePreserving :
    MeasurePreserving (velocityFlip (E := E)) ((volume : Measure E).prod volume)
      ((volume : Measure E).prod volume) := by
  exact (MeasurePreserving.id (volume : Measure E)).prod
    (Measure.measurePreserving_neg (volume : Measure E))

theorem flipped_verlet_measurePreserving (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (fun z => velocityFlip (verlet g h z))
      ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
  velocityFlip_measurePreserving.comp (verlet_measurePreserving g hg h)

end PersistencePays

#print axioms PersistencePays.verlet_measurePreserving
#print axioms PersistencePays.flipped_verlet_measurePreserving
