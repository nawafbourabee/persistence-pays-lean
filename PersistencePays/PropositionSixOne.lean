import PersistencePays.NormalizedEpochConditions
import PersistencePays.WarmEpochCount
import PersistencePays.FreeTransportTheorem
import PersistencePays.GradientCost

/-! Proposition 6.1 for the literal adjusted epoch chain. No analytic estimate
is assumed: the remaining assumptions are the explicit scalar parameter tests
(a)--(d), subsequently discharged by the main parameter construction. -/
noncomputable section
namespace PersistencePays.OBABOPath
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem proposition_6_1_with_warm_bound
    {U:E→ℝ} {L LH h vstar M ε:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν] (hac:ν≪phaseGibbs U)
    (hM:1≤M) (hW:warmL2 ν (phaseGibbs U)≤ENNReal.ofReal M)
    (hε:0<ε) (hε1:ε≤1) (n:ℕ)
    (c:NormalizedEpochConditions L LH h vstar
      (samplingRadius (Module.finrank ℝ E) (samplingEpochs ε) M ε) (Module.finrank ℝ E) n) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let P := epochKernel U a.twice_contDiff.continuous.measurable (gradient U) hg h
      (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) (n+1)
    probabilityTV (iterateKernel P (samplingEpochs ε) ∘ₘ ν) (phaseGibbs U)≤ENNReal.ofReal ε := by
  let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
  let r:=Real.exp (-h)
  let σ:=Real.sqrt (1-Real.exp (-2*h))
  let N:=samplingEpochs ε
  let R:=samplingRadius (Module.finrank ℝ E) N M ε
  let D:= {z:E×E|phaseEnergy U z≤R}
  let K:=unadjustedEpochKernel (gradient U) hg h r σ (n+1)
  let π:=phaseGibbs U
  letI:IsProbabilityMeasure (positionGibbs U):=a.gibbs_isProbabilityMeasure
  letI:IsProbabilityMeasure π:=by unfold π phaseGibbs; infer_instance
  have hD:MeasurableSet D := measurableSet_le (by
    have hU:=a.twice_contDiff.continuous
    unfold phaseEnergy
    fun_prop) measurable_const
  have hnorm:r^2+σ^2=1 := (normalized_ou_coefficients h c.step_pos.le).2.2.2.1
  have hlocal (z:E×E) (hz:z∈D) : probabilityTV (K z) π≤ENNReal.ofReal (0.105:ℝ) ∧
      epochRejectionProbability U (gradient U) h r σ (n+1) z≤ENNReal.ofReal (0.0102:ℝ) :=
    proposition_6_1_local a a2 a.gaussianSmoothedFreeTransportBound hstar hzero n c z hz
  have hpair (z:E×E) (hz:z∈D) (z':E×E) (hz':z'∈D) :
      probabilityTV (K z) (K z')+epochRejectionProbability U (gradient U) h r σ (n+1) z+
      epochRejectionProbability U (gradient U) h r σ (n+1) z'≤(1/4:ℝ≥0∞) := by
    have ht:probabilityTV (K z) (K z')≤probabilityTV (K z) π+probabilityTV (K z') π := by
      simpa only [probabilityTV_symm π] using probabilityTV_triangle (K z) π (K z')
    calc
      _ ≤ ENNReal.ofReal (0.105:ℝ)+ENNReal.ofReal (0.105:ℝ)+
          ENNReal.ofReal (0.0102:ℝ)+ENNReal.ofReal (0.0102:ℝ) :=
        add_le_add (add_le_add (ht.trans (add_le_add (hlocal z hz).1 (hlocal z' hz').1))
          (hlocal z hz).2) (hlocal z' hz').2
      _ ≤ _ := by
        rw [←ENNReal.ofReal_add (by norm_num) (by norm_num),
          ←ENNReal.ofReal_add (by norm_num) (by norm_num),
          ←ENNReal.ofReal_add (by norm_num) (by norm_num),
          show (1/4:ℝ≥0∞)=ENNReal.ofReal (1/4:ℝ) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hc:=proposition_5_3_of_bound U a.twice_contDiff.continuous.measurable a.gibbs_integrable
    (gradient U) hg h r σ hnorm (n+1) ν hac D hD (1/4) hpair N
  have htail:(N:ℝ≥0∞)*π Dᶜ≤ENNReal.ofReal (ε^2/(16*M^2)) :=
    a.samplingRadius_tail hstar hzero (samplingEpochs_pos hε hε1) (by linarith) hε
  exact hc.trans (localized_error_numeric hM hε hε1 (samplingEpochs_quarter_power hε hε1) htail hW)

theorem proposition_6_1
    {U:E→ℝ} {L LH h vstar ε:ℝ} (a:A1 U 1 L) (a2:A2 U LH)
    (hstar:a.minimizer=0) (hzero:U 0=0)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν] (hac:ν≪phaseGibbs U)
    (hW:warmL2 ν (phaseGibbs U)≠∞) (hε:0<ε) (hε1:ε≤1) (n:ℕ)
    (c:NormalizedEpochConditions L LH h vstar
      (samplingRadius (Module.finrank ℝ E) (samplingEpochs ε) (warmL2 ν (phaseGibbs U)).toReal ε)
      (Module.finrank ℝ E) n) :
    let hg := (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    let P := epochKernel U a.twice_contDiff.continuous.measurable (gradient U) hg h
      (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) (n+1)
    probabilityTV (iterateKernel P (samplingEpochs ε) ∘ₘ ν) (phaseGibbs U)≤ENNReal.ofReal ε := by
  letI:IsProbabilityMeasure (positionGibbs U):=a.gibbs_isProbabilityMeasure
  letI:IsProbabilityMeasure (phaseGibbs U):=by unfold phaseGibbs; infer_instance
  have hM:1≤(warmL2 ν (phaseGibbs U)).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hW (one_le_warmL2 ν (phaseGibbs U) hac)
  exact proposition_6_1_with_warm_bound a a2 hstar hzero ν hac hM
    (by rw [ENNReal.ofReal_toReal hW]) hε hε1 n c

/-- Every attempted step, including rejected attempts, costs one gradient after
one initial cache evaluation. This is the literal implementation cost. -/
theorem proposition_6_1_gradient_cost (U:E→ℝ) (g:E→E) (h ε:ℝ) (n:ℕ)
    (ξ ξ':ℕ→ℕ→E) (ell:ℕ→ℝ) (z:E×E) :
    (CachedOBABO.runEpochs U g h (Real.exp (-h)) (Real.sqrt (1-Real.exp (-2*h))) ξ ξ' ell (n+1)
      (CachedOBABO.initializeCache g z 0) (samplingEpochs ε)).calls=samplingEpochs ε*(n+1)+1 :=
  CachedOBABO.total_gradient_queries U g h _ _ ξ ξ' ell (n+1) (samplingEpochs ε) z

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.proposition_6_1
#print axioms PersistencePays.OBABOPath.proposition_6_1_gradient_cost
