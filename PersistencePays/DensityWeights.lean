import PersistencePays.ConvexMatrixDivergence

/-! Exact real-density integral and integrability conversion. -/
open MeasureTheory Filter
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem real_density_integrable_iff (ν:Measure E) {n:E→ℝ}
    (hn:Measurable n) (hn0:∀ x,0≤n x)
    (hν:ν=volume.withDensity (fun x => ENNReal.ofReal (n x))) (f:E→F) :
    Integrable f ν ↔ Integrable (fun x => n x • f x) volume := by
  rw [hν]
  simpa only [ENNReal.toReal_ofReal (hn0 _)] using
    (integrable_withDensity_iff_integrable_smul' hn.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g:=f))

theorem real_density_integral (ν:Measure E) {n:E→ℝ}
    (hn:Measurable n) (hn0:∀ x,0≤n x)
    (hν:ν=volume.withDensity (fun x => ENNReal.ofReal (n x))) (f:E→F) :
    (∫ x,f x ∂ν) = ∫ x,n x • f x := by
  rw [hν,integral_withDensity_eq_integral_toReal_smul hn.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hn0 x)]

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.real_density_integrable_iff
