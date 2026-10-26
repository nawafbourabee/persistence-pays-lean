import PersistencePays.GaussianLatentDefs
import PersistencePays.PhaseGaussianRegularization

/-! Exact Gaussian regression obtained by an orthogonal change of the two
independent Gaussian noises. These are equalities of actual probability laws. -/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace PersistencePays
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def latentFlight (ε s:ℝ) (z ξ:E×E):E×E :=
  (z.1+ε•ξ.1+s•(z.2+ε•ξ.2),z.2+ε•ξ.2)

def latentRegression (ε s:ℝ) (z ξ:E×E):E×E :=
  let y:=latentCenter s z+observationNoise ε s•ξ.1
  (y,regressionBeta s•y+regressionLatentMean s z+regressionNoise ε s•ξ.2)

def regressionRotation (s:ℝ) (ξ:E×E):E×E :=
  Prod.swap (gaussianReflection (s/Real.sqrt (1+s^2)) (1/Real.sqrt (1+s^2)) ξ)

lemma regressionRotation_preserving (s:ℝ) :
    MeasurePreserving (regressionRotation (E:=E) s)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  have ha:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have has: (Real.sqrt (1+s^2))^2=1+s^2 := Real.sq_sqrt (by positivity)
  have hn:(s/Real.sqrt (1+s^2))^2+(1/Real.sqrt (1+s^2))^2=1 := by
    rw [div_pow,div_pow,← add_div,has]
    field_simp
    ring
  exact Measure.measurePreserving_swap.comp
    (gaussianReflection_preserving _ _ hn (by positivity))

lemma latentFlight_regressionRotation (ε s:ℝ) (z ξ:E×E) :
    latentFlight ε s z (regressionRotation s ξ)=latentRegression ε s z ξ := by
  have ha:0<Real.sqrt (1+s^2) := Real.sqrt_pos.mpr (by positivity)
  have has: (Real.sqrt (1+s^2))^2=1+s^2 := Real.sq_sqrt (by positivity)
  have hcoef : 1/Real.sqrt (1+s^2)+s*(s/Real.sqrt (1+s^2))=Real.sqrt (1+s^2) := by
    field_simp
    nlinarith [has]
  have hzero : -(s/Real.sqrt (1+s^2))+s*(1/Real.sqrt (1+s^2))=0 := by ring
  have hb : regressionBeta s*observationNoise ε s=ε*(s/Real.sqrt (1+s^2)) := by
    dsimp [regressionBeta,observationNoise]
    field_simp [ha.ne',show 1+s^2≠0 by positivity]
    rw [has]
    ring
  apply Prod.ext
  · change z.1+ε•((1/Real.sqrt (1+s^2))•ξ.1-(s/Real.sqrt (1+s^2))•ξ.2)+
      s•(z.2+ε•((s/Real.sqrt (1+s^2))•ξ.1+(1/Real.sqrt (1+s^2))•ξ.2))=
      latentCenter s z+observationNoise ε s•ξ.1
    calc
      _ = latentCenter s z+ε•((1/Real.sqrt (1+s^2)+s*(s/Real.sqrt (1+s^2)))•ξ.1+
        (-(s/Real.sqrt (1+s^2))+s*(1/Real.sqrt (1+s^2)))•ξ.2) := by dsimp [latentCenter]; module
      _ = _ := by rw [hcoef,hzero,zero_smul,add_zero,smul_smul]; rfl
  · change z.2+ε•((s/Real.sqrt (1+s^2))•ξ.1+(1/Real.sqrt (1+s^2))•ξ.2)=
      regressionBeta s•(latentCenter s z+observationNoise ε s•ξ.1)+
        regressionLatentMean s z+regressionNoise ε s•ξ.2
    rw [regressionLatentMean_identity]
    simp only [smul_add,smul_smul,hb]
    dsimp [regressionNoise]
    module

lemma latentFlight_law (ε s:ℝ) (z:E×E) :
    ((stdGaussian E).prod (stdGaussian E)).map (latentFlight ε s z)=
      ((stdGaussian E).prod (stdGaussian E)).map (latentRegression ε s z) := by
  have h := regressionRotation_preserving (E:=E) s
  calc
    _ = (((stdGaussian E).prod (stdGaussian E)).map (regressionRotation s)).map
        (latentFlight ε s z) := by rw [h.map_eq]
    _ = _ := by
      rw [Measure.map_map (by unfold latentFlight; fun_prop) h.measurable]
      congr 1
      funext ξ
      exact latentFlight_regressionRotation ε s z ξ

end
end PersistencePays
#print axioms PersistencePays.latentFlight_law
