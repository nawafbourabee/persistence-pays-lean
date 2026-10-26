import PersistencePays.GaussianReflection

/-! Explicit coefficients for Gaussian regularization followed by free transport.
The noise scale is ε, so the paper's ι equals ε². -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regressionBeta (s:ℝ):ℝ := s/(1+s^2)
def regressionNoise (ε s:ℝ):ℝ := ε/Real.sqrt (1+s^2)
def observationNoise (ε s:ℝ):ℝ := ε*Real.sqrt (1+s^2)
def latentCenter (s:ℝ) (z:E×E):E := z.1+s•z.2
def regressionLatentMean (s:ℝ) (z:E×E):E := (1+s^2)⁻¹•(z.2-s•z.1)
def regressionScore (ε s:ℝ) (z:E×E):E := (ε^2*(1+s^2))⁻¹•latentCenter s z
def regressionLogWeight (ε s:ℝ) (z:E×E):ℝ :=
  -‖latentCenter s z‖^2/(2*ε^2*(1+s^2))
def regressionExponent (ε s:ℝ) (q:E×(E×E)):ℝ :=
  ⟪regressionScore ε s q.2,q.1⟫+regressionLogWeight ε s q.2

theorem regressionLatentMean_identity (s:ℝ) (z:E×E) :
    regressionLatentMean s z=z.2-regressionBeta s • latentCenter s z := by
  have hn:1+s^2≠0 := by positivity
  have hc:(1+s^2)⁻¹=1-s^2*(1+s^2)⁻¹ := by field_simp [hn]; ring
  dsimp [regressionLatentMean,regressionBeta,latentCenter]
  calc
    _ = (1+s^2)⁻¹•z.2-(s*(1+s^2)⁻¹)•z.1 := by module
    _ = (1-s^2*(1+s^2)⁻¹)•z.2-(s*(1+s^2)⁻¹)•z.1 := by rw [← hc]
    _ = _ := by module

end PersistencePays
#print axioms PersistencePays.regressionLatentMean_identity
