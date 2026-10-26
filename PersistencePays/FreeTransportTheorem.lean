import PersistencePays.CompactLatentReduction
import PersistencePays.CompactGaussianFreeTransport

/-! Unconditional free-transport corrector inequality. The Gaussian smooth
case is proved from the actual law; truncation and entropy convergence then
remove the auxiliary smoothness and support conditions. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
universe u
variable {E:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.gaussianSmoothedFreeTransportBound {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    GaussianSmoothedFreeTransportBound a := by
  apply a.gaussianSmoothedBound_of_compactBalls
  intro R ν ε hε t ht
  exact a.compactGaussian_freeTransport (ν:Measure (CompactLatentBall E R))
    Subtype.val continuous_subtype_val hε ht

/-- Lemma 4.8 with the manuscript's actual assumptions and no analytic premise. -/
theorem A1.lemma_4_8 {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (μ:ProbabilityMeasure (E×E)) (hμ:MemLp id 2 (μ:Measure (E×E)))
    (hK:klDiv (μ:Measure (E×E)) (phaseGibbs U)≠∞) {t:ℝ} (ht:0<t) :
    a.corrector (transportJoint (μ:Measure (E×E)) t)-a.corrector (μ:Measure (E×E))≤
      freeTransportRHS (μ:Measure (E×E)) (positionGibbs U) t :=
  a.free_transport_of_smoothed_bound a.gaussianSmoothedFreeTransportBound μ hμ hK ht
end PersistencePays
#print axioms PersistencePays.A1.gaussianSmoothedFreeTransportBound
#print axioms PersistencePays.A1.lemma_4_8
