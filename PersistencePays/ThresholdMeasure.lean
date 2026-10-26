import PersistencePays.Volume

/-!
# Measure-theoretic threshold correction

This file proves the change-of-variables part of Lemma 2.3, including the
switching boundary. No conclusion about OU preservation is assumed here.
-/

noncomputable section
namespace PersistencePays
open MeasureTheory Set
open scoped ENNReal
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

theorem preserving_piecewise_id (μ : Measure α) (T : α → α)
    (hT : MeasurePreserving T μ μ) (A : Set α) (hA : MeasurableSet A)
    (hTA : T ⁻¹' A = A) :
    MeasurePreserving (A.piecewise T id) μ μ := by
  classical
  have hm : Measurable (A.piecewise T id) :=
    hT.measurable.piecewise hA measurable_id
  have hp : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
    simpa only [hTA] using hT.restrict_preimage hA
  have hp' : MeasurePreserving (A.piecewise T id) (μ.restrict A) (μ.restrict A) := by
    apply hp.congr hm
    filter_upwards [ae_restrict_mem hA] with x hx
    simp [hx]
  have hc : MeasurePreserving (A.piecewise T id) (μ.restrict Aᶜ) (μ.restrict Aᶜ) := by
    apply (MeasurePreserving.id (μ.restrict Aᶜ)).congr hm
    filter_upwards [ae_restrict_mem hA.compl] with x hx
    simp only [mem_compl_iff] at hx
    simp [hx]
  simpa only [Measure.restrict_add_restrict_compl hA] using hp'.add_measure hc

theorem preserving_withDensity (μ : Measure α) (T : α → α)
    (hT : MeasurePreserving T μ μ) (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
    (hinv : ∀ x, ρ (T x) = ρ x) :
    MeasurePreserving T (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hT.measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply hT.measurable hA,
    withDensity_apply _ (hT.measurable hA), withDensity_apply _ hA]
  simpa only [hinv] using hT.setLIntegral_comp_preimage hA hρ

def extendedProposal (H : α → ℝ) (T : α → α) (z : α × ℝ) : α × ℝ :=
  (T z.1, z.2 - energyIncrement H T z.1)

def positiveAcceptSet (H : α → ℝ) (T : α → α) : Set (α × ℝ) :=
  {z | 0 < z.2 ∧ energyIncrement H T z.1 < z.2}

def globalThresholdMap (H : α → ℝ) (T : α → α) : α × ℝ → α × ℝ :=
  (positiveAcceptSet H T).piecewise (extendedProposal H T) id

theorem extendedProposal_measurable (H : α → ℝ) (hH : Measurable H)
    (T : α → α) (hT : Measurable T) : Measurable (extendedProposal H T) := by
  exact (hT.comp measurable_fst).prodMk
    (measurable_snd.sub (((hH.comp hT).sub hH).comp measurable_fst))

theorem positiveAcceptSet_measurable (H : α → ℝ) (hH : Measurable H)
    (T : α → α) (hT : Measurable T) : MeasurableSet (positiveAcceptSet H T) := by
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt (((hH.comp hT).sub hH).comp measurable_fst) measurable_snd)

theorem extendedProposal_preserving (μ : Measure α) [SFinite μ]
    (H : α → ℝ) (hH : Measurable H) (T : α → α)
    (hT : MeasurePreserving T μ μ) :
    MeasurePreserving (extendedProposal H T) (μ.prod volume) (μ.prod volume) := by
  exact hT.skew_product
    (measurable_snd.sub (((hH.comp hT.measurable).sub hH).comp measurable_fst))
    (ae_of_all _ (fun x =>
      (measurePreserving_sub_right (volume : Measure ℝ) (energyIncrement H T x)).map_eq))

theorem extendedProposal_acceptSet (H : α → ℝ) (T : α → α)
    (hT : Function.Involutive T) :
    extendedProposal H T ⁻¹' positiveAcceptSet H T = positiveAcceptSet H T := by
  ext z
  simp only [mem_preimage, positiveAcceptSet, mem_setOf_eq, extendedProposal,
    involutive_energyIncrement H T hT]
  constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]

theorem globalThresholdMap_preserving (μ : Measure α) [SFinite μ]
    (H : α → ℝ) (hH : Measurable H) (T : α → α)
    (hTm : MeasurePreserving T μ μ) (hTi : Function.Involutive T) :
    MeasurePreserving (globalThresholdMap H T) (μ.prod volume) (μ.prod volume) :=
  preserving_piecewise_id _ _ (extendedProposal_preserving μ H hH T hTm) _
    (positiveAcceptSet_measurable H hH T hTm.measurable)
    (extendedProposal_acceptSet H T hTi)

theorem globalThresholdMap_energy (H : α → ℝ) (T : α → α) (z : α × ℝ) :
    H (globalThresholdMap H T z).1 + (globalThresholdMap H T z).2 = H z.1 + z.2 := by
  classical
  unfold globalThresholdMap Set.piecewise
  split_ifs
  · simp only [extendedProposal, energyIncrement]
    ring
  · rfl

theorem globalThresholdMap_positive_iff (H : α → ℝ) (T : α → α) (z : α × ℝ) :
    0 < (globalThresholdMap H T z).2 ↔ 0 < z.2 := by
  classical
  unfold globalThresholdMap Set.piecewise
  split_ifs with hz
  · have hh := hz.2
    simp only [extendedProposal]
    exact iff_of_true (sub_pos.mpr hh) hz.1
  · rfl

theorem globalThresholdMap_eq (H : α → ℝ) (T : α → α) (z : α × ℝ) (hz : 0 < z.2) :
    globalThresholdMap H T z = thresholdMap H T z := by
  classical
  simp [globalThresholdMap, positiveAcceptSet, thresholdMap, Set.piecewise,
    hz, extendedProposal]

def extendedGibbs (μ : Measure α) (H : α → ℝ) : Measure (α × ℝ) :=
  ((μ.prod volume).withDensity (fun z => ENNReal.ofReal (Real.exp (-(H z.1 + z.2))))).restrict
    {z | 0 < z.2}

/-- The threshold correction preserves the exact Gibbs-exponential measure,
including its positive-threshold support and both branches. -/
theorem thresholdMap_preserves_extendedGibbs (μ : Measure α) [SFinite μ]
    (H : α → ℝ) (hH : Measurable H) (T : α → α)
    (hTm : MeasurePreserving T μ μ) (hTi : Function.Involutive T) :
    MeasurePreserving (thresholdMap H T) (extendedGibbs μ H) (extendedGibbs μ H) := by
  have hg := globalThresholdMap_preserving μ H hH T hTm hTi
  have hρ : Measurable (fun z : α × ℝ => ENNReal.ofReal (Real.exp (-(H z.1 + z.2)))) :=
    (((hH.comp measurable_fst).add measurable_snd).neg.exp).ennreal_ofReal
  have hd := preserving_withDensity (μ.prod volume) (globalThresholdMap H T) hg _ hρ
    (fun z => by rw [globalThresholdMap_energy])
  have hpos : MeasurableSet {z : α × ℝ | 0 < z.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hp : globalThresholdMap H T ⁻¹' {z : α × ℝ | 0 < z.2} = {z | 0 < z.2} := by
    ext z
    exact globalThresholdMap_positive_iff H T z
  have hr := hd.restrict_preimage hpos
  rw [hp] at hr
  apply hr.congr
  · unfold thresholdMap
    exact ((hTm.measurable.comp measurable_fst).prodMk
      (measurable_snd.sub (((hH.comp hTm.measurable).sub hH).comp measurable_fst))).ite
      (measurableSet_lt (((hH.comp hTm.measurable).sub hH).comp measurable_fst)
        measurable_snd) measurable_id
  · filter_upwards [ae_restrict_mem hpos] with z hz
    exact globalThresholdMap_eq H T z hz

theorem lifted_symmetry_preserves_extendedGibbs (μ : Measure α) [SFinite μ]
    (H : α → ℝ) (hH : Measurable H) (S : α → α)
    (hS : MeasurePreserving S μ μ) (hHS : ∀ x, H (S x) = H x) :
    MeasurePreserving (fun z : α × ℝ => (S z.1, z.2))
      (extendedGibbs μ H) (extendedGibbs μ H) := by
  have hprod := hS.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hρ : Measurable (fun z : α × ℝ => ENNReal.ofReal (Real.exp (-(H z.1 + z.2)))) :=
    (((hH.comp measurable_fst).add measurable_snd).neg.exp).ennreal_ofReal
  have hd := preserving_withDensity (μ.prod volume) (fun z => (S z.1, z.2)) hprod _ hρ
    (fun z => by rw [hHS])
  exact hd.restrict_preimage (measurableSet_lt measurable_const measurable_snd)

section ActualVerlet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem phaseEnergy_measurable (U : E → ℝ) (hU : Measurable U) :
    Measurable (phaseEnergy U) := by
  unfold phaseEnergy
  fun_prop

/-- The actual accepted-Verlet / rejected-flip branch in Definition 2.2
preserves the Gibbs-exponential measure. This theorem includes the switching
boundary and uses literal Verlet, rather than an assumed abstract invariant map. -/
theorem verlet_adjusted_preserves_extendedGibbs (U : E → ℝ) (hU : Measurable U)
    (g : E → E) (hg : Measurable g) (h : ℝ) :
    MeasurePreserving (adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h))
      (extendedGibbs ((volume : Measure E).prod volume) (phaseEnergy U))
      (extendedGibbs ((volume : Measure E).prod volume) (phaseEnergy U)) := by
  have henergy := phaseEnergy_measurable U hU
  have ht := thresholdMap_preserves_extendedGibbs
    ((volume : Measure E).prod volume) (phaseEnergy U) henergy
    (velocityFlip ∘ verlet g h) (flipped_verlet_measurePreserving g hg h)
    (flipped_verlet_involutive g h)
  have hs := lifted_symmetry_preserves_extendedGibbs
    ((volume : Measure E).prod volume) (phaseEnergy U) henergy
    velocityFlip velocityFlip_measurePreserving (phaseEnergy_velocityFlip U)
  have hc := hs.comp ht
  have he : (fun z : (E × E) × ℝ =>
      (velocityFlip (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).1,
        (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).2)) =
      adjustedUpdate (phaseEnergy U) velocityFlip (verlet g h) :=
    funext (verlet_thresholdMap_adjustedUpdate U g h)
  change MeasurePreserving (fun z : (E × E) × ℝ =>
      (velocityFlip (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).1,
        (thresholdMap (phaseEnergy U) (velocityFlip ∘ verlet g h) z).2)) _ _ at hc
  rwa [he] at hc
end ActualVerlet

end PersistencePays

#print axioms PersistencePays.thresholdMap_preserves_extendedGibbs
#print axioms PersistencePays.verlet_adjusted_preserves_extendedGibbs
