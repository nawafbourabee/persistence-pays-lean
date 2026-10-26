import PersistencePays.BrenierInverse
import PersistencePays.Corrector
import Mathlib.Probability.Kernel.Disintegration.Integral

/-! Actual conditional-kernel gluing of couplings, for quadratic transport stability. -/
noncomputable section
namespace PersistencePays.QuadraticTransport
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glueMeasure (π ρ : ProbabilityMeasure (E × E)) : Measure ((E × E) × E) :=
  (π : Measure (E × E)) ⊗ₘ (ρ : Measure (E × E)).condKernel.comap Prod.snd measurable_snd

instance glueMeasure_probability (π ρ : ProbabilityMeasure (E × E)) :
    IsProbabilityMeasure (glueMeasure π ρ) := by unfold glueMeasure; infer_instance

theorem glueMeasure_left (π ρ : ProbabilityMeasure (E × E)) :
    (glueMeasure π ρ).map Prod.fst = (π : Measure (E × E)) := by
  exact Measure.fst_compProd _ _

theorem glueMeasure_right (π ρ : ProbabilityMeasure (E × E))
    (hmatch : (π : Measure (E × E)).snd=(ρ : Measure (E × E)).fst) :
    (glueMeasure π ρ).map (fun z => (z.1.2,z.2)) = (ρ : Measure (E × E)) := by
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA, glueMeasure,
    Measure.compProd_apply (hA.preimage (by fun_prop))]
  simp only [Kernel.comap_apply]
  change (∫⁻ p : E × E, (ρ : Measure (E × E)).condKernel p.2 (Prod.mk p.2 ⁻¹' A) ∂(π : Measure (E × E))) = _
  have hm := Kernel.measurable_kernel_prodMk_left (κ := (ρ : Measure (E × E)).condKernel) hA
  rw [← lintegral_map hm measurable_snd]
  change (∫⁻ b, (ρ : Measure (E × E)).condKernel b (Prod.mk b ⁻¹' A) ∂(π : Measure (E × E)).snd) = _
  rw [hmatch, ← Measure.compProd_apply hA, Measure.disintegrate _ _]

def gluedPlan (π ρ : ProbabilityMeasure (E × E)) : ProbabilityMeasure (E × E) :=
  ⟨(glueMeasure π ρ).map (fun z => (z.1.1,z.2)),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

theorem gluedPlan_mem (μ ν ξ : ProbabilityMeasure E) (π ρ : ProbabilityMeasure (E × E))
    (hπ : π ∈ plans μ ν) (hρ : ρ ∈ plans ν ξ) : gluedPlan π ρ ∈ plans μ ξ := by
  have hmatch : (π : Measure (E × E)).snd=(ρ : Measure (E × E)).fst :=
    (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.2).trans
      (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hρ.1).symm
  constructor
  · apply Subtype.ext
    change ((glueMeasure π ρ).map (fun z => (z.1.1,z.2))).map Prod.fst = (μ : Measure E)
    rw [Measure.map_map measurable_fst (by fun_prop)]
    have he := congrArg (fun q : Measure (E × E) => q.map Prod.fst) (glueMeasure_left π ρ)
    rw [Measure.map_map measurable_fst measurable_fst] at he
    exact he.trans (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hπ.1)
  · apply Subtype.ext
    change ((glueMeasure π ρ).map (fun z => (z.1.1,z.2))).map Prod.snd = (ξ : Measure E)
    rw [Measure.map_map measurable_snd (by fun_prop)]
    have he := congrArg (fun q : Measure (E × E) => q.map Prod.snd) (glueMeasure_right π ρ hmatch)
    rw [Measure.map_map measurable_snd (by fun_prop)] at he
    exact he.trans (congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hρ.2)

end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.gluedPlan_mem
