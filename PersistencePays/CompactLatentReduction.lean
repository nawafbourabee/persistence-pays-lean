import PersistencePays.FreeTransportLimit
import PersistencePays.GaussianFlightConditional
import Mathlib.MeasureTheory.Measure.Restrict

/-! A bounded law, including a singular one, is exactly the image of a
probability law on a compact ball. This discharges the latent parametrization
used in the smooth-case proof. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Set
universe u
variable {E:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev CompactLatentBall (E:Type u) [NormedAddCommGroup E] (R:ℝ) :=
  Metric.closedBall (0:E×E) R

instance compactLatentBall_compact (R:ℝ) : CompactSpace (CompactLatentBall E R) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E×E) R)

def compactLatentBallLaw (ν:Measure (E×E)) (R:ℝ):Measure (CompactLatentBall E R) :=
  ν.comap Subtype.val

theorem compactLatentBallLaw_probability (ν:Measure (E×E)) [IsProbabilityMeasure ν]
    {R:ℝ} (hb:∀ᵐ z ∂ν,‖z‖≤R) : IsProbabilityMeasure (compactLatentBallLaw ν R) := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_closedBall).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe,Metric.mem_closedBall,dist_zero_right] using hb

theorem compactLatentBallLaw_map (ν:Measure (E×E)) {R:ℝ}
    (hb:∀ᵐ z ∂ν,‖z‖≤R) :
    (compactLatentBallLaw ν R).map (Subtype.val:CompactLatentBall E R→E×E)=ν := by
  rw [compactLatentBallLaw,map_comap_subtype_coe measurableSet_closedBall]
  exact Measure.restrict_eq_self_of_ae_mem (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb)

theorem additiveNoise_eq_fullGaussianOU (ν:ProbabilityMeasure (E×E)) (ε:ℝ) :
    (additiveNoiseProbability ν gaussianPairProbability ε:Measure (E×E))=
      fullGaussianOUKernel 1 ε ∘ₘ (ν:Measure (E×E)) := by
  rw [fullGaussianOUKernel_comp_map]
  simp only [one_smul,additiveNoiseProbability_coe]

def compactLatentBallPushforward {R:ℝ} (ν:ProbabilityMeasure (CompactLatentBall E R)) :
    ProbabilityMeasure (E×E) := ν.map measurable_subtype_coe.aemeasurable

/-- Exact reduction to a compact latent presentation. The displayed premise is
only the smooth analytic inequality; no probability or approximation facts
remain in it. -/
theorem A1.gaussianSmoothedBound_of_compactBalls {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (hcompact:∀(R:ℝ)(ν:ProbabilityMeasure (CompactLatentBall E R)),
      ∀ε:ℝ,0<ε→∀t:ℝ,0<t→
      a.corrector (transportJoint (fullGaussianOUKernel 1 ε ∘ₘ
        (compactLatentBallPushforward ν:Measure (E×E))) t)-
      a.corrector (fullGaussianOUKernel 1 ε ∘ₘ (compactLatentBallPushforward ν:Measure (E×E)))≤
      freeTransportRHS (fullGaussianOUKernel 1 ε ∘ₘ (compactLatentBallPushforward ν:Measure (E×E))) (positionGibbs U) t) :
    GaussianSmoothedFreeTransportBound a := by
  intro ν hb ε hε t ht
  obtain ⟨R,hR⟩:=hb
  have hp:=compactLatentBallLaw_probability (ν:Measure (E×E)) hR
  let νc:ProbabilityMeasure (CompactLatentBall E R):=⟨compactLatentBallLaw (ν:Measure (E×E)) R,hp⟩
  have heq:compactLatentBallPushforward νc=ν:=by
    apply Subtype.ext
    exact compactLatentBallLaw_map _ hR
  have hh:=hcompact R νc ε hε t ht
  simp only [heq] at hh
  simpa only [additiveNoise_eq_fullGaussianOU] using hh
end PersistencePays
#print axioms PersistencePays.A1.gaussianSmoothedBound_of_compactBalls
