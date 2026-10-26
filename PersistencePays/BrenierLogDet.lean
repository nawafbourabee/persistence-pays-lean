import PersistencePays.BrenierHessian
import PersistencePays.SymmetricLogDet

/-! A measurable SPD Brenier Hessian together with the integrable signed
log-determinant identity needed by Appendix A. -/
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal RealInnerProductSpace
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem brenier_positive_logdet_entropy (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hμca : volume ≪ (μ : Measure E))
    (hνac : (ν : Measure E) ≪ volume)
    (hμlog : Integrable (fun x => Real.log (((μ : Measure E).rnDeriv volume x).toReal)) μ)
    (hνlog : Integrable (fun x => Real.log (((ν : Measure E).rnDeriv volume x).toReal)) ν) :
    ∃ (s : Set E) (G : E → E →L[ℝ] E),
      MeasurableSet s ∧ volume sᶜ=0 ∧ Measurable G ∧
      (∀ᵐ x ∂(μ : Measure E),
        HasFDerivWithinAt (brenierMap μ ν) (G x) s x ∧
        (G x).toLinearMap.IsSymmetric ∧ ∀ v : E, v≠0 → 0<⟪v,G x v⟫) ∧
      Integrable (fun x => Real.log (G x).det) μ ∧
      (∫ x, Real.log (G x).det ∂(μ : Measure E)) =
        boltzmannEntropy (μ : Measure E)-boltzmannEntropy (ν : Measure E) := by
  obtain ⟨s,G,hs,hs0,hG,_,hd,hJ⟩ :=
    brenier_measurable_positive_jacobian μ ν hμ hν hμac hμca hνac
  have hlog := entropy_change_of_density_identity μ ν hμac hνac
    (measurable_brenierMap μ ν) (brenierMap_spec μ ν hμ hν hμac).2.1 hJ hμlog hνlog
  have he : (fun x => Real.log |(G x).det|) =ᵐ[(μ : Measure E)]
      (fun x => Real.log (G x).det) := by
    filter_upwards [hd] with x hx
    have hp : 0<(G x).det := symmetric_positive_det (G x).toLinearMap hx.2.1 hx.2.2
    rw [abs_of_pos hp]
  refine ⟨s,G,hs,hs0,hG,hd,hlog.1.congr he,?_⟩
  rw [← integral_congr_ae he]
  exact hlog.2

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenier_positive_logdet_entropy
