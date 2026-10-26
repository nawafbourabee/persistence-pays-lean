import PersistencePays.ConditionalDensityBound

/-! Finite Gibbs entropy follows from an actual finite Lebesgue-density cap
and integrability of the Gibbs energy, even for singular latent mixture laws. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
variable {S:Type*} [MeasurableSpace S]

theorem integrable_llr_of_integrable_upper (μ ν:Measure S)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac:μ≪ν)
    (F:S→ℝ) (hF:Integrable F μ) (hb:∀ᵐ x∂μ,llr μ ν x≤F x) :
    Integrable (llr μ ν) μ := by
  have hn:=neg_llr hac
  apply (hF.norm.add (Measure.integrable_toReal_rnDeriv (μ:=ν) (ν:=μ))).mono'
    (measurable_llr μ ν).aestronglyMeasurable
  filter_upwards [hb,hn] with x hx hnx
  have hl:=Real.log_le_self (ENNReal.toReal_nonneg (a:=ν.rnDeriv μ x))
  change -llr μ ν x=Real.log (ν.rnDeriv μ x).toReal at hnx
  change ‖llr μ ν x‖ ≤ ‖F x‖+(ν.rnDeriv μ x).toReal
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [abs_nonneg (F x)]
  · exact hx.trans ((le_abs_self (F x)).trans
      (le_add_of_nonneg_right ENNReal.toReal_nonneg))

theorem gibbs_entropy_finite_of_density_cap (ξ:Measure S) [SigmaFinite ξ] [NeZero ξ]
    (H:S→ℝ) (hHI:Integrable (fun x=>Real.exp (-H x)) ξ)
    (μ:Measure S) [IsProbabilityMeasure μ] (hHμ:Integrable H μ)
    (D:ℝ) (hD:0<D) (hcap:μ≤ENNReal.ofReal D • ξ) :
    klDiv μ (ξ.tilted (-H))≠∞ := by
  letI : IsProbabilityMeasure (ξ.tilted (-H)):=isProbabilityMeasure_tilted hHI
  have hac:μ≪ξ:=hcap.absolutelyContinuous.trans
    ((Measure.AbsolutelyContinuous.refl ξ).smul_left _)
  have hact:μ≪ξ.tilted (-H):=hac.trans (absolutelyContinuous_tilted hHI)
  apply klDiv_ne_top hact
  exact integrable_llr_of_integrable_upper μ _ hact _
    ((hHμ.add (integrable_const _)).add (integrable_const _))
    (llr_gibbs_le_density_cap ξ H hHI μ D hD hcap)

end PersistencePays
#print axioms PersistencePays.gibbs_entropy_finite_of_density_cap
