import PersistencePays.GaussianMeanField
import PersistencePays.RankOneDivergence

/-! Explicit posterior covariance field for the Gaussian free-flight mixture. -/
noncomputable section
namespace PersistencePays
open MeasureTheory
open scoped RealInnerProductSpace
variable {E Z:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace Z]

/-- Covariance of a bounded latent vector under its affine exponential posterior,
plus an isotropic Gaussian covariance. -/
def affinePosteriorCovariance (μ:Measure Z) (F H:Z→E) (k:Z→ℝ) (τ:ℝ) (y:E):E→L[ℝ]E :=
  affinePosteriorMean μ (fun z=>(innerSL ℝ (F z)).smulRight (F z)) H k y-
    (innerSL ℝ (affinePosteriorMean μ F H k y)).smulRight (affinePosteriorMean μ F H k y)+
    τ•ContinuousLinearMap.id ℝ E

def gaussianRegressionCovariance (μ:Measure Z) (g:Z→E×E) (ε s:ℝ) (y:E):E→L[ℝ]E :=
  affinePosteriorCovariance μ (fun z=>regressionLatentMean s (g z))
    (fun z=>regressionScore ε s (g z)) (fun z=>regressionLogWeight ε s (g z))
    (ε^2/(1+s^2)) y

end PersistencePays
