import PersistencePays.McCannJacobian
import PersistencePays.PositionBoltzmannEntropy

/-! Integrability and the exact entropy change of the actual Brenier Jacobian.
The logarithm identity is first established a.e. on positive finite densities;
no subtraction of undefined differential entropies is used. -/
open Set Filter MeasureTheory MeasureTheory.Measure InformationTheory
open scoped Topology ENNReal
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem log_jacobian_of_density_identity
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμac : μ ≪ volume) (hνac : ν ≪ volume)
    {T : E → E} (hT : Measurable T) (hmap : μ.map T=ν) {A : E → E →L[ℝ] E}
    (hJ : μ.rnDeriv volume =ᵐ[volume] fun x =>
      ENNReal.ofReal |(A x).det| * ν.rnDeriv volume (T x)) :
    ∀ᵐ x ∂μ, (A x).det≠0 ∧
      Real.log |(A x).det| = Real.log ((μ.rnDeriv volume x).toReal) -
        Real.log ((ν.rnDeriv volume (T x)).toReal) := by
  have hv : ∀ᵐ x ∂μ, 0<ν.rnDeriv volume (T x) ∧ ν.rnDeriv volume (T x)≠∞ := by
    have hh := (Measure.rnDeriv_pos hνac).and
      (hνac.ae_le (Measure.rnDeriv_ne_top ν volume))
    have hh' : ∀ᵐ y ∂μ.map T, 0<ν.rnDeriv volume y ∧ ν.rnDeriv volume y≠∞ := by
      rwa [hmap]
    exact ae_of_ae_map hT.aemeasurable hh'
  filter_upwards [hμac.ae_le hJ,Measure.rnDeriv_pos hμac,
    hμac.ae_le (Measure.rnDeriv_ne_top μ volume),hv] with x hx hp hfin hq
  have hp' := ENNReal.toReal_pos (ne_of_gt hp) hfin
  have hq' := ENNReal.toReal_pos (ne_of_gt hq.1) hq.2
  have hr := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at hr
  have hdet : 0 < |(A x).det| := (mul_pos_iff_of_pos_right hq').mp (hr ▸ hp')
  refine ⟨abs_pos.mp hdet,?_⟩
  rw [hr,Real.log_mul hdet.ne' hq'.ne']
  ring

theorem entropy_change_of_density_identity
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμac : μ ≪ volume) (hνac : ν ≪ volume)
    {T : E → E} (hT : Measurable T) (hmap : μ.map T=ν) {A : E → E →L[ℝ] E}
    (hJ : μ.rnDeriv volume =ᵐ[volume] fun x =>
      ENNReal.ofReal |(A x).det| * ν.rnDeriv volume (T x))
    (hμlog : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)) μ)
    (hνlog : Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) ν) :
    Integrable (fun x => Real.log |(A x).det|) μ ∧
      (∫ x, Real.log |(A x).det| ∂μ) = boltzmannEntropy μ-boltzmannEntropy ν := by
  have he : (fun x => Real.log |(A x).det|) =ᵐ[μ]
      (fun x => Real.log ((μ.rnDeriv volume x).toReal) -
        Real.log ((ν.rnDeriv volume (T x)).toReal)) :=
    (log_jacobian_of_density_identity μ ν hμac hνac hT hmap hJ).mono
    (fun _ h => h.2)
  have hcomp : Integrable (fun x => Real.log ((ν.rnDeriv volume (T x)).toReal)) μ := by
    have hh : Integrable (fun x => Real.log ((ν.rnDeriv volume x).toReal)) (μ.map T) := by
      rwa [hmap]
    exact (integrable_map_measure
      (Measure.measurable_rnDeriv ν volume).ennreal_toReal.log.aestronglyMeasurable
      hT.aemeasurable).mp hh
  refine ⟨(hμlog.sub hcomp).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_sub hμlog hcomp]
  have hm : (∫ x, Real.log ((ν.rnDeriv volume (T x)).toReal) ∂μ) = boltzmannEntropy ν := by
    unfold boltzmannEntropy
    have hh := integral_map (μ:=μ) hT.aemeasurable
      (Measure.measurable_rnDeriv ν volume).ennreal_toReal.log.aestronglyMeasurable
    rw [hmap] at hh
    exact hh.symm
  rw [hm]
  rfl

/-- Genuine McCann entropy identity, with integrability of the log determinant
proved from integrability of the two actual log densities. -/
theorem brenier_entropy_change (μ ν : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) (hν : MemLp id 2 (ν : Measure E))
    (hμac : (μ : Measure E) ≪ volume) (hμca : volume ≪ (μ : Measure E))
    (hνac : (ν : Measure E) ≪ volume)
    (hμlog : Integrable (fun x => Real.log (((μ : Measure E).rnDeriv volume x).toReal)) μ)
    (hνlog : Integrable (fun x => Real.log (((ν : Measure E).rnDeriv volume x).toReal)) ν) :
    ∃ s : Set E, MeasurableSet s ∧ volume sᶜ=0 ∧
      InjOn (brenierMap μ ν) s ∧ DifferentiableOn ℝ (brenierMap μ ν) s ∧
      Integrable (fun x => Real.log |(fderivWithin ℝ (brenierMap μ ν) s x).det|) μ ∧
      (∫ x, Real.log |(fderivWithin ℝ (brenierMap μ ν) s x).det| ∂(μ : Measure E)) =
        boltzmannEntropy (μ : Measure E)-boltzmannEntropy (ν : Measure E) := by
  obtain ⟨s,hs,hs0,hinj,hd,hJ⟩ := brenier_density_jacobian μ ν hμ hν hμac hμca hνac
  exact ⟨s,hs,hs0,hinj,hd,entropy_change_of_density_identity μ ν hμac hνac
    (measurable_brenierMap μ ν) (brenierMap_spec μ ν hμ hν hμac).2.1 hJ hμlog hνlog⟩

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.brenier_entropy_change
