import PersistencePays.ConvexDivergence
import PersistencePays.BrenierLogDet
import PersistencePays.GibbsCutoff
import PersistencePays.EntropyMoment
import PersistencePays.QuadraticDistance

/-! Talagrand's quadratic transport inequality for the actual strongly convex
Gibbs law. Brenier transport, rough convex differentiability, the density
Jacobian, the signed divergence inequality, and all moment/entropy conditions
are proved dependencies. No LSI or transport-entropy inequality is assumed. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.brenier_entropy_displacement_nonneg {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:ProbabilityMeasure E) (hK:klDiv (ν:Measure E) (positionGibbs U)≠∞) :
    0≤boltzmannEntropy (ν:Measure E)-boltzmannEntropy (positionGibbs U)+
      (∫ x,⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ ∂positionGibbs U) := by
  classical
  letI : IsProbabilityMeasure (positionGibbs U) := a.gibbs_isProbabilityMeasure
  have hν := a.memLp_two_of_entropy_finite (ν:Measure E) hK
  have hμac : positionGibbs U≪(volume:Measure E) := tilted_absolutelyContinuous volume (-U)
  have hμca : (volume:Measure E)≪positionGibbs U := absolutelyContinuous_tilted a.gibbs_integrable
  have hνac := (klDiv_ne_top_iff.mp hK).1.trans hμac
  have hνlog := (gibbs_boltzmann_identity U a.gibbs_integrable (ν:Measure E)
    (a.potential_integrable hν) hK).1
  have hμlog := (gibbs_boltzmann_identity U a.gibbs_integrable (positionGibbs U)
    (a.potential_integrable a.position_memLp_two) (by simp)).1
  obtain ⟨s,G,hs,hs0,hG,hd,hlog,hent⟩ :=
    QuadraticTransport.brenier_positive_logdet_entropy a.gibbsProbability ν
      a.position_memLp_two hν hμac hμca hνac hμlog hνlog
  obtain ⟨φ,hφ,_,hφT⟩ := QuadraticTransport.brenierMap_global_convex_gradient
    a.gibbsProbability ν a.position_memLp_two hν hμac hμca
  change a.gibbsBrenierMap ν =ᵐ[positionGibbs U] gradient φ at hφT
  change ∀ᵐ x ∂positionGibbs U,
    HasFDerivWithinAt (a.gibbsBrenierMap ν) (G x) s x ∧
    (G x).toLinearMap.IsSymmetric ∧ ∀ v:E,v≠0 → 0<⟪v,G x v⟫_ℝ at hd
  change Integrable (fun x => Real.log (G x).det) (positionGibbs U) at hlog
  change (∫ x,Real.log (G x).det ∂positionGibbs U)=
    boltzmannEntropy (positionGibbs U)-boltzmannEntropy (ν:Measure E) at hent
  have hdv : ∀ᵐ x ∂(volume:Measure E),
      HasFDerivWithinAt (a.gibbsBrenierMap ν) (G x) s x ∧
        (G x).toLinearMap.IsSymmetric ∧ ∀ v:E,v≠0 → 0<⟪v,G x v⟫_ℝ := hμca.ae_le hd
  have hpos : ∀ᵐ x ∂(volume:Measure E),∀ v:E,0≤⟪v,G x v⟫_ℝ := by
    filter_upwards [hdv] with x hx
    intro v
    by_cases hv:v=0
    · simp [hv]
    · exact (hx.2.2 v hv).le
  let b := stdOrthonormalBasis ℝ E
  have htrace : Measurable (fun x => LinearMap.trace ℝ E (G x).toLinearMap) := by
    have he (x:E) : LinearMap.trace ℝ E (G x).toLinearMap = ∑ i,⟪b i,G x (b i)⟫_ℝ :=
      LinearMap.trace_eq_sum_inner _ b
    simp_rw [he]
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.inner
      ((ContinuousLinearMap.apply ℝ E (b i)).continuous.measurable.comp hG)
  have htrace0 : ∀ᵐ x ∂(volume:Measure E),0≤LinearMap.trace ℝ E (G x).toLinearMap := by
    filter_upwards [hpos] with x hx
    rw [LinearMap.trace_eq_sum_inner _ b]
    exact Finset.sum_nonneg (fun i _ => hx (b i))
  have hTi := (a.gibbsBrenierMap_spec ν hν).2.2
  have hdiv := a.gibbs_divergence_from_compact (a.gibbsBrenierMap ν) hTi
    (fun x => LinearMap.trace ℝ E (G x).toLinearMap) htrace htrace0
    (fun η hη hc h0 => QuadraticTransport.compact_convex_divergence hφ (hμca.ae_le hφT)
      hs0 hG (hdv.mono (fun _ h => h.1)) hpos hη hc h0)
  have hlogle := integral_mono_ae hlog (hdiv.1.sub (integrable_const (Module.finrank ℝ E:ℝ)))
    (hd.mono (fun x hx => symmetric_logdet_le_trace (G x).toLinearMap hx.2.1 hx.2.2))
  simp only [Pi.sub_apply] at hlogle
  rw [integral_sub hdiv.1 (integrable_const _)] at hlogle
  simp only [integral_const,probReal_univ,one_smul] at hlogle
  have hforce := integrable_inner_of_memLp_two (a.gradient_memLp a.position_memLp_two) hTi
  have hid := integrable_inner_of_memLp_two (a.gradient_memLp a.position_memLp_two) a.position_memLp_two
  simp only [id_eq] at hforce hid
  have he : (∫ x,⟪gradient U x,a.gibbsBrenierMap ν x-x⟫_ℝ ∂positionGibbs U) =
      (∫ x,⟪gradient U x,a.gibbsBrenierMap ν x⟫_ℝ ∂positionGibbs U)-(Module.finrank ℝ E:ℝ) := by
    simp_rw [inner_sub_right]
    rw [integral_sub hforce hid,a.gibbs_stein_identity]
  rw [he]
  linarith [hdiv.2]

/-- Sharp Talagrand inequality, with the actual quadratic optimal-coupling cost.
Finite second moments follow from finite KL and are not extra hypotheses. -/
theorem A1.talagrand_cost {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:ProbabilityMeasure E) (hK:klDiv (ν:Measure E) (positionGibbs U)≠∞) :
    (QuadraticTransport.cost ν a.gibbsProbability).toReal ≤
      2/m*(klDiv (ν:Measure E) (positionGibbs U)).toReal := by
  have hν := a.memLp_two_of_entropy_finite (ν:Measure E) hK
  have hl := a.gibbsBrenier_entropy_lower_bound ν hν hK
  have hn := a.brenier_entropy_displacement_nonneg ν hK
  have hb : m/2*(QuadraticTransport.cost a.gibbsProbability ν).toReal ≤
      (klDiv (ν:Measure E) (positionGibbs U)).toReal := by linarith
  rw [QuadraticTransport.cost_comm ν a.gibbsProbability]
  calc
    _ ≤ (klDiv (ν:Measure E) (positionGibbs U)).toReal/(m/2) :=
      (le_div_iff₀ (by linarith [a.m_pos])).mpr (by nlinarith [hb])
    _ = _ := by field_simp

theorem A1.talagrand_cost_ennreal {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:ProbabilityMeasure E) :
    QuadraticTransport.cost ν a.gibbsProbability ≤
      ENNReal.ofReal (2/m)*klDiv (ν:Measure E) (positionGibbs U) := by
  by_cases hK:klDiv (ν:Measure E) (positionGibbs U)=∞
  · rw [hK,ENNReal.mul_top (by exact (ENNReal.ofReal_pos.mpr (by positivity [a.m_pos])).ne')]
    exact le_top
  have hν := a.memLp_two_of_entropy_finite (ν:Measure E) hK
  have hc := QuadraticTransport.cost_finite ν a.gibbsProbability
    hν.integrable_norm_pow' a.position_memLp_two.integrable_norm_pow'
  have hh := ENNReal.ofReal_le_ofReal (a.talagrand_cost ν hK)
  rwa [ENNReal.ofReal_toReal hc,ENNReal.ofReal_mul (by positivity [a.m_pos]),
    ENNReal.ofReal_toReal hK] at hh

theorem A1.talagrand_wasserstein {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:ProbabilityMeasure E) (hK:klDiv (ν:Measure E) (positionGibbs U)≠∞) :
    QuadraticTransport.wassersteinTwo ν a.gibbsProbability ≤
      Real.sqrt (2/m*(klDiv (ν:Measure E) (positionGibbs U)).toReal) :=
  Real.sqrt_le_sqrt (a.talagrand_cost ν hK)

end PersistencePays
#print axioms PersistencePays.A1.brenier_entropy_displacement_nonneg
#print axioms PersistencePays.A1.talagrand_cost_ennreal
#print axioms PersistencePays.A1.talagrand_wasserstein
