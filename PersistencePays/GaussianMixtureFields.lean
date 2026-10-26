import PersistencePays.GaussianFlightDensity
import PersistencePays.GaussianSingleMomentum
import PersistencePays.CompactMixtureDerivative

/-! Continuity and momentum conservation for the actual compact Gaussian mixture. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

def singleFlightFlux (ε s:ℝ) (y:E) (z:E×E):E :=
  singleFlightDensity ε s y z•singleFlightVelocity s y z

def gaussianFlightFlux (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E :=
  ∫z,singleFlightFlux ε s y (g z) ∂μ

def gaussianFlightSecondMoment (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E→L[ℝ]E :=
  ∫z,singleFlightMoment ε s y (g z) ∂μ

lemma singleFlightFlux_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>singleFlightFlux ε p.1.1 p.1.2 p.2) :=
  (singleFlightDensity_contDiff n hε).smul (singleFlightVelocity_contDiff n)

lemma singleFlightMoment_contDiff (n:ℕ) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>singleFlightMoment ε p.1.1 p.1.2 p.2) := by
  have hn:=singleFlightDensity_contDiff (E:=E) n hε
  have hb:=singleFlightVelocity_contDiff (E:=E) n
  let R:(E→L[ℝ]ℝ)→L[ℝ]E→L[ℝ]E→L[ℝ]E:=ContinuousLinearMap.smulRightL ℝ E E
  have hR:ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>
      (innerSL ℝ (singleFlightVelocity p.1.1 p.1.2 p.2)).smulRight
        (singleFlightVelocity p.1.1 p.1.2 p.2)) := by
    change ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>R
      (innerSL ℝ (singleFlightVelocity p.1.1 p.1.2 p.2)) (singleFlightVelocity p.1.1 p.1.2 p.2))
    exact (R.contDiff.comp ((innerSL ℝ).contDiff.comp hb)).clm_apply hb
  have hcoef:ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>ε^2/(1+p.1.1^2)) :=
    contDiff_const.div (contDiff_const.add (contDiff_fst.fst.pow 2)) (fun p=>by positivity)
  have hI:ContDiff ℝ n (fun p:(ℝ×E)×(E×E)=>
      (ε^2/(1+p.1.1^2))•ContinuousLinearMap.id ℝ E) := hcoef.smul contDiff_const
  exact (hn.smul hR).add (hn.smul hI)

lemma gaussianFlightFlux_contDiff (n:ℕ) (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (gaussianFlightFlux μ g ε).uncurry :=
  compact_mixture_integral_contDiff n μ g hg _ (singleFlightFlux_contDiff n hε)

lemma gaussianFlightSecondMoment_contDiff (n:ℕ) (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) :
    ContDiff ℝ n (gaussianFlightSecondMoment μ g ε).uncurry :=
  compact_mixture_integral_contDiff n μ g hg _ (singleFlightMoment_contDiff n hε)

lemma compact_latent_deriv_integrable {V:Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {F:ℝ×(E×E)→V} (hF:ContDiff ℝ 1 F) (s:ℝ) :
    Integrable (fun z=>deriv (fun t=>F (t,g z)) s) μ := by
  have hc:=((compact_partial_fderiv_continuous hF).comp
    ((continuous_const (y:=s)).prodMk hg)).clm_apply (continuous_const (y:=(1:ℝ)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


end PersistencePays
#print axioms PersistencePays.gaussianFlightSecondMoment_contDiff
