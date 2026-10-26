import PersistencePays.PotentialNormalization
import PersistencePays.GaussianTarget
import PersistencePays.IsotropicObservation
import PersistencePays.WarmL2
import PersistencePays.Pinsker

/-! Exact coordinate normalization of the Gibbs law and sampling criteria.
The minimizer enters only this proof coordinate map, not the algorithm. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma tilted_add_constant {S:Type*} [MeasurableSpace S]
    (μ:Measure S) (f:S→ℝ) (c:ℝ) :
    μ.tilted (fun x=>f x+c)=μ.tilted f := by
  unfold Measure.tilted
  simp_rw [Real.exp_add]
  rw [integral_mul_const]
  apply withDensity_congr_ae
  filter_upwards with x
  congr 1
  by_cases hZ:(∫x,Real.exp (f x)∂μ)=0
  · simp [hZ]
  · field_simp

theorem warmL2_map_equiv {S T:Type*} [MeasurableSpace S] [MeasurableSpace T]
    (e:S≃ᵐT) (ν μ:Measure S) [SigmaFinite ν] [SigmaFinite μ] :
    warmL2 (ν.map e) (μ.map e)=warmL2 ν μ := by
  unfold warmL2
  rw [e.measurableEmbedding.eLpNorm_map_measure]
  apply eLpNorm_congr_ae
  exact (e.measurableEmbedding.rnDeriv_map ν μ).mono (fun x hx=>congrArg ENNReal.toReal hx)

theorem probabilityTV_map_le {S T:Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ ν:Measure S) {f:S→T} (hf:Measurable f) :
    probabilityTV (μ.map f) (ν.map f)≤probabilityTV μ ν := by
  apply iSup_le
  intro A
  apply iSup_le
  intro hA
  simp only [Measure.real,Measure.map_apply hf hA]
  exact le_iSup_of_le (f ⁻¹' A) (le_iSup_of_le (hf hA) le_rfl)

theorem probabilityTV_map_equiv {S T:Type*} [MeasurableSpace S] [MeasurableSpace T]
    (e:S≃ᵐT) (μ ν:Measure S) :
    probabilityTV (μ.map e) (ν.map e)=probabilityTV μ ν := by
  apply le_antisymm (probabilityTV_map_le μ ν e.measurable)
  have hh:=probabilityTV_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self,Measure.map_id] using hh

variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def A1.normalizationPosition {U:E→ℝ} {m L:ℝ} (a:A1 U m L):E≃ᵐE :=
  gaussianAffineEquiv (isotropicScale (Real.sqrt m) (Real.sqrt_pos.mpr a.m_pos).ne')
    (-Real.sqrt m • a.minimizer)

def A1.normalizationState {U:E→ℝ} {m L:ℝ} (a:A1 U m L):(E×E)≃ᵐ(E×E) :=
  a.normalizationPosition.prodCongr (MeasurableEquiv.refl E)

theorem A1.normalizationPosition_apply {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x:E) :
    a.normalizationPosition x=Real.sqrt m • (x-a.minimizer) := by
  change Real.sqrt m • x+(-Real.sqrt m) • a.minimizer=_
  module

theorem A1.normalizationPosition_symm_apply {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (y:E) :
    a.normalizationPosition.symm y=a.minimizer+(Real.sqrt m)⁻¹•y := by
  apply a.normalizationPosition.injective
  rw [MeasurableEquiv.apply_symm_apply,a.normalizationPosition_apply]
  simp [smul_smul,(Real.sqrt_pos.mpr a.m_pos).ne']

theorem A1.normalizationState_apply {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (z:E×E) :
    a.normalizationState z=(Real.sqrt m • (z.1-a.minimizer),z.2) := by
  change (a.normalizationPosition z.1,z.2)=_
  rw [a.normalizationPosition_apply]

theorem A1.normalizationPosition_gibbs {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    (positionGibbs U).map a.normalizationPosition=positionGibbs a.normalizedPotential := by
  unfold positionGibbs
  rw [map_tilted_equiv _ _ _ a.twice_contDiff.continuous.measurable.neg]
  change ((volume:Measure E).map (gaussianAffineEquiv _ _)).tilted _=_
  rw [map_volume_gaussianAffineEquiv]
  unfold inverseJacobian
  rw [tilted_smul_positive _ _ (abs_pos.mpr (inv_ne_zero
    (isotropicScale (Real.sqrt m) (Real.sqrt_pos.mpr a.m_pos).ne').toLinearEquiv.isUnit_det'.ne_zero))]
  · have he:(fun y=>-U (a.normalizationPosition.symm y))=
        (fun y=>-a.normalizedPotential y+(-U a.minimizer)) := by
      funext y
      rw [a.normalizationPosition_symm_apply]
      simp only [A1.normalizedPotential,scaledPotential]
      ring
    change volume.tilted (fun y=>-U (a.normalizationPosition.symm y))=_
    rw [he,tilted_add_constant]
    rfl
  · exact a.twice_contDiff.continuous.measurable.neg.comp a.normalizationPosition.symm.measurable

theorem A1.normalizationState_gibbs {U:E→ℝ} {m L:ℝ} (a:A1 U m L) :
    (phaseGibbs U).map a.normalizationState=phaseGibbs a.normalizedPotential := by
  have hh:=Measure.map_prod_map (positionGibbs U) (stdGaussian E)
    a.normalizationPosition.measurable measurable_id
  rw [a.normalizationPosition_gibbs,Measure.map_id] at hh
  exact hh.symm

theorem A1.normalizationState_warmL2 {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:Measure (E×E)) [SigmaFinite ν] :
    warmL2 (ν.map a.normalizationState) (phaseGibbs a.normalizedPotential)=
      warmL2 ν (phaseGibbs U) := by
  rw [←a.normalizationState_gibbs]
  exact warmL2_map_equiv a.normalizationState _ _

theorem A1.normalizationState_TV {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (ν:Measure (E×E)) :
    probabilityTV (ν.map a.normalizationState) (phaseGibbs a.normalizedPotential)=
      probabilityTV ν (phaseGibbs U) := by
  rw [←a.normalizationState_gibbs]
  exact probabilityTV_map_equiv a.normalizationState _ _

theorem A1.normalizationState_absolutelyContinuous {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    {ν:Measure (E×E)} (hν:ν≪phaseGibbs U) :
    ν.map a.normalizationState≪phaseGibbs a.normalizedPotential := by
  rw [←a.normalizationState_gibbs]
  exact a.normalizationState.measurableEmbedding.absolutelyContinuous_map hν

end PersistencePays
#print axioms PersistencePays.A1.normalizationState_gibbs
#print axioms PersistencePays.A1.normalizationState_warmL2
#print axioms PersistencePays.A1.normalizationState_TV
