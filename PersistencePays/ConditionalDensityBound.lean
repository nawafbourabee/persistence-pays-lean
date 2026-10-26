import PersistencePays.ConditioningEntropy
import PersistencePays.GibbsPartitionBound
import PersistencePays.PhaseGibbsDensity
import PersistencePays.KickEntropy

/-! Entropy of an exceptional conditioned component from a genuine Lebesgue
density cap and its exceptional energy. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal

section General
variable {S:Type*} [MeasurableSpace S]

theorem rnDeriv_le_density_cap (μ ξ:Measure S) [IsFiniteMeasure μ] [SigmaFinite ξ]
    (C:ℝ≥0∞) (hc:μ≤C • ξ) : ∀ᵐ x∂ξ,μ.rnDeriv ξ x≤C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ξ)
  intro A hA hAf
  calc
    (∫⁻x in A,μ.rnDeriv ξ x ∂ξ) ≤ μ A := Measure.setLIntegral_rnDeriv_le A
    _ ≤ (C • ξ) A := hc A
    _ = ∫⁻_ in A,C ∂ξ := by simp [Measure.smul_apply,smul_eq_mul]

theorem llr_gibbs_le_density_cap (ξ:Measure S) [SigmaFinite ξ] [NeZero ξ]
    (H:S→ℝ) (hHI:Integrable (fun x=>Real.exp (-H x)) ξ)
    (μ:Measure S) [IsProbabilityMeasure μ] (D:ℝ) (hD:0<D)
    (hcap:μ≤ENNReal.ofReal D • ξ) :
    ∀ᵐ x∂μ,llr μ (ξ.tilted (-H)) x≤H x+Real.log (∫y,Real.exp (-H y)∂ξ)+max (Real.log D) 0 := by
  have hac : μ≪ξ := hcap.absolutelyContinuous.trans
    ((Measure.AbsolutelyContinuous.refl ξ).smul_left _)
  have hbound := rnDeriv_le_density_cap μ ξ (ENNReal.ofReal D) hcap
  have hr := toReal_rnDeriv_tilted_right μ ξ hHI
  have hZ : 0<∫y,Real.exp (-H y)∂ξ := integral_exp_pos hHI
  filter_upwards [hac.ae_le hr,hac.ae_le hbound,Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top μ ξ)] with x hx hbx hp hf
  have hp' : 0<(μ.rnDeriv ξ x).toReal := ENNReal.toReal_pos (ne_of_gt hp) hf
  have hb' : (μ.rnDeriv ξ x).toReal≤D := by
    simpa only [ENNReal.toReal_ofReal hD.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbx
  have hlog := Real.log_le_log hp' hb'
  simp only [neg_neg] at hx
  change (μ.rnDeriv (ξ.tilted (-H)) x).toReal =
    Real.exp (H x)*(∫y,Real.exp (-H y)∂ξ)*(μ.rnDeriv ξ x).toReal at hx
  unfold llr
  rw [hx,Real.log_mul (mul_pos (Real.exp_pos _) hZ).ne' hp'.ne',
    Real.log_mul (Real.exp_ne_zero _) hZ.ne',Real.log_exp]
  linarith [le_max_left (Real.log D) 0]

theorem conditioned_gibbs_entropy_density_cap (ξ:Measure S) [SigmaFinite ξ] [NeZero ξ]
    (H:S→ℝ) (hHI:Integrable (fun x=>Real.exp (-H x)) ξ)
    (μ:Measure S) [IsProbabilityMeasure μ] (hHμ:Integrable H μ)
    (hK:klDiv μ (ξ.tilted (-H))≠∞) (D:ℝ) (hD:0<D)
    (hcap:μ≤ENNReal.ofReal D • ξ) (A:Set S) (hA:MeasurableSet A) (hpos:μ A≠0) :
    (μ A).toReal*(klDiv (cond μ A) (ξ.tilted (-H))).toReal ≤
      (∫x in A,H x∂μ)+(μ A).toReal*
        (Real.log (∫y,Real.exp (-H y)∂ξ)+max (Real.log D) 0+Real.log (1/(μ A).toReal)) := by
  letI : IsProbabilityMeasure (ξ.tilted (-H)) := isProbabilityMeasure_tilted hHI
  have hb := llr_gibbs_le_density_cap ξ H hHI μ D hD hcap
  have hi := (klDiv_ne_top_iff.mp hK).2
  have hj : Integrable (fun x=>H x+Real.log (∫y,Real.exp (-H y)∂ξ)+max (Real.log D) 0) μ :=
    (hHμ.add (integrable_const _)).add (integrable_const _)
  have ht := integral_mono_ae (μ:=μ.restrict A) hi.restrict hj.restrict (Measure.restrict_le_self.absolutelyContinuous.ae_le hb)
  have hfirst : Integrable (fun x=>H x+Real.log (∫y,Real.exp (-H y)∂ξ)) (μ.restrict A) :=
    hHμ.restrict.add (integrable_const _)
  rw [integral_add hfirst (integrable_const _),
    integral_add hHμ.restrict (integrable_const _)] at ht
  rw [(conditional_klDiv μ _ hK A hA hpos).2]
  simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul] at ht
  rw [one_div,Real.log_inv]
  linarith
end General

end PersistencePays
#print axioms PersistencePays.conditioned_gibbs_entropy_density_cap
