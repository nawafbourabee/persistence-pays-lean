import PersistencePays.PropositionSixOne
import PersistencePays.MainParameterConditions
import PersistencePays.MainGradientComplexity
import PersistencePays.NormalizationKernel
import PersistencePays.CachedEpochSampler

/-! Theorem 1 for the actual cached implementation, with every scalar parameter
condition discharged. The coordinate normalization is only a proof device:
the implemented sampler uses the original potential and its actual gradient. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory OBABOPath
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma A2.constant_nonneg_of_dimension {U:E→ℝ} {LH:ℝ} (a2:A2 U LH)
    (hd:1≤Module.finrank ℝ E) : 0≤LH := by
  let :Nontrivial E:=Module.nontrivial_of_finrank_pos (lt_of_lt_of_le Nat.zero_lt_one hd)
  obtain ⟨x,hx⟩:=exists_ne (0:E)
  have h:=a2.lipschitz x 0
  simp only [sub_zero] at h
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  exact nonneg_of_mul_nonneg_left (le_trans (norm_nonneg _) h) hn

/-- The normalized main theorem, with the explicit parameter choice and no
remaining parameter tests. -/
theorem A1.theorem_one_normalized {U:E→ℝ} {L LH ε:ℝ}
    (a:A1 U 1 L) (a2:A2 U LH) (hstar:a.minimizer=0) (hzero:U 0=0)
    (hd:1≤Module.finrank ℝ E) (ν:Measure (E×E)) [IsProbabilityMeasure ν]
    (hac:ν≪phaseGibbs U) (hW:warmL2 ν (phaseGibbs U)≠∞)
    (hε:0<ε) (hε1:ε≤1) :
    let M:=(warmL2 ν (phaseGibbs U)).toReal
    let D:=(Module.finrank ℝ E:ℝ)+Real.log (M/ε)
    let t:=mainStep L LH D
    let n:=mainEpochPredecessor L LH D
    let hg:=(contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    probabilityTV
      (iterateKernel (epochKernel U a.twice_contDiff.continuous.measurable
        (gradient U) hg t (Real.exp (-t)) (Real.sqrt (1-Real.exp (-2*t))) (n+1))
        (samplingEpochs ε) ∘ₘ ν) (phaseGibbs U)≤ENNReal.ofReal ε := by
  let :IsProbabilityMeasure (positionGibbs U):=a.gibbs_isProbabilityMeasure
  let :IsProbabilityMeasure (phaseGibbs U):=by unfold phaseGibbs; infer_instance
  have hM:1≤(warmL2 ν (phaseGibbs U)).toReal := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono hW (one_le_warmL2 ν (phaseGibbs U) hac)
  exact proposition_6_1 a a2 hstar hzero ν hac hW hε hε1 _
    (main_warm_parameters (Module.finrank ℝ E) hd a.m_le_L
      (a2.constant_nonneg_of_dimension hd) hM hε hε1)

/-- The arbitrary-m kernel statement: friction is 2 sqrt(m), so each half-OU
coefficient is exp(-sqrt(m)h), and every accept/reject decision is retained. -/
theorem A1.theorem_one_kernel {U:E→ℝ} {m L LH ε:ℝ}
    (a:A1 U m L) (a2:A2 U LH) (hd:1≤Module.finrank ℝ E)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν]
    (hac:ν≪phaseGibbs U) (hW:warmL2 ν (phaseGibbs U)≠∞)
    (hε:0<ε) (hε1:ε≤1) :
    let κ:=L/m
    let lH:=LH/m^(3/2:ℝ)
    let M:=(warmL2 ν (phaseGibbs U)).toReal
    let D:=(Module.finrank ℝ E:ℝ)+Real.log (M/ε)
    let t:=mainStep κ lH D
    let n:=mainEpochPredecessor κ lH D
    let hg:=(contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable
    probabilityTV
      (iterateKernel (epochKernel U a.twice_contDiff.continuous.measurable
        (gradient U) hg (t/Real.sqrt m) (Real.exp (-t))
          (Real.sqrt (1-Real.exp (-2*t))) (n+1)) (samplingEpochs ε) ∘ₘ ν)
      (phaseGibbs U)≤ENNReal.ofReal ε := by
  let νn:=ν.map a.normalizationState
  let :IsProbabilityMeasure νn:=Measure.isProbabilityMeasure_map a.normalizationState.measurable.aemeasurable
  have hνn:νn≪phaseGibbs a.normalizedPotential:=a.normalizationState_absolutelyContinuous hac
  have hWn:warmL2 νn (phaseGibbs a.normalizedPotential)≠∞:=by
    rw [a.normalizationState_warmL2]
    exact hW
  have hn:=a.normalizedPotential_A1.theorem_one_normalized (a.normalizedPotential_A2 a2)
    a.normalizedPotential_minimizer a.normalizedPotential_zero hd νn hνn hWn hε hε1
  dsimp only at hn ⊢
  simp only [νn,a.normalizationState_warmL2] at hn
  let t:=mainStep (L/m) (LH/m^(3/2:ℝ))
    ((Module.finrank ℝ E:ℝ)+Real.log ((warmL2 ν (phaseGibbs U)).toReal/ε))
  have ht:Real.sqrt m*(t/Real.sqrt m)=t:=by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr a.m_pos)]
  dsimp only [t] at ht
  rw [iterateKernel_comp_eq_evolve] at hn ⊢
  rw [←a.normalizationState_TV]
  rw [a.normalization_epoch_laws]
  simpa only [ht] using hn

/-- Full Theorem 1 for finite Gaussian/threshold arrays. The output law has
TV error at most epsilon. Every realized run uses exactly N*steps+1 gradient
evaluations, including initialization, rejected proposals, and all epochs.
No minimizer oracle or other gradient preprocessing is used. -/
theorem A1.theorem_one {U:E→ℝ} {m L LH ε:ℝ}
    (a:A1 U m L) (a2:A2 U LH) (hd:1≤Module.finrank ℝ E)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν]
    (hac:ν≪phaseGibbs U) (hW:warmL2 ν (phaseGibbs U)≠∞)
    (hε:0<ε) (hε1:ε≤1) :
    let κ:=L/m
    let lH:=LH/m^(3/2:ℝ)
    let M:=(warmL2 ν (phaseGibbs U)).toReal
    let D:=(Module.finrank ℝ E:ℝ)+Real.log (M/ε)
    let t:=mainStep κ lH D
    let steps:=mainEpochPredecessor κ lH D+1
    let N:=samplingEpochs ε
    let run:=CachedOBABO.simulate U (gradient U) (t/Real.sqrt m)
      (Real.exp (-t)) (Real.sqrt (1-Real.exp (-2*t))) steps N
    probabilityTV
      ((ν.prod (Measure.pi (fun _:Fin N=>epochRandomness (E:=E) steps))).map
        (fun p=>(run p.1 p.2).phase)) (phaseGibbs U)≤ENNReal.ofReal ε ∧
      (∀ z b,(run z b).calls=N*steps+1) ∧
      ((N*steps+1:ℕ):ℝ)≤
        (10:ℝ)^30*(mainLogScale κ lH D)^(3/2:ℝ)*
          (Real.sqrt (κ*D)+Real.sqrt lH*D^(3/4:ℝ))*Real.log (2/ε)+1 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [CachedOBABO.simulate_random_start_law U a.twice_contDiff.continuous.measurable
      (gradient U) (contDiff_gradient_of_twice_contDiff U a.twice_contDiff).continuous.measurable]
    exact a.theorem_one_kernel a2 hd ν hac hW hε hε1
  · intro z b
    exact CachedOBABO.simulate_queries_exact _ _ _ _ _ _ _ _ _
  · let :IsProbabilityMeasure (positionGibbs U):=a.gibbs_isProbabilityMeasure
    let :IsProbabilityMeasure (phaseGibbs U):=by unfold phaseGibbs; infer_instance
    have hM:1≤(warmL2 ν (phaseGibbs U)).toReal:=by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono hW (one_le_warmL2 ν (phaseGibbs U) hac)
    have hD:1≤(Module.finrank ℝ E:ℝ)+Real.log ((warmL2 ν (phaseGibbs U)).toReal/ε):=
      (main_radius_bounds (Module.finrank ℝ E) hd hM hε hε1).1
    have hκ:1≤L/m:=(le_div_iff₀ a.m_pos).mpr (by simpa using a.m_le_L)
    have hlH:0≤LH/m^(3/2:ℝ):=div_nonneg (a2.constant_nonneg_of_dimension hd) (Real.rpow_nonneg a.m_pos.le _)
    have hc:=main_gradient_complexity hκ hlH hD hε hε1
    push_cast at hc ⊢
    linarith


/-- The prescribed physical step and both finite loop lengths are strictly
positive, including the zero-Hessian-Lipschitz case. -/
theorem A1.theorem_one_parameter_validity {U:E→ℝ} {m L LH ε:ℝ}
    (a:A1 U m L) (a2:A2 U LH) (hd:1≤Module.finrank ℝ E)
    (ν:Measure (E×E)) [IsProbabilityMeasure ν]
    (hac:ν≪phaseGibbs U) (hW:warmL2 ν (phaseGibbs U)≠∞)
    (hε:0<ε) (hε1:ε≤1) :
    let κ:=L/m
    let lH:=LH/m^(3/2:ℝ)
    let D:=(Module.finrank ℝ E:ℝ)+Real.log ((warmL2 ν (phaseGibbs U)).toReal/ε)
    0 < mainStep κ lH D/Real.sqrt m ∧
      1 ≤ mainEpochPredecessor κ lH D+1 ∧ 1 ≤ samplingEpochs ε := by
  let :IsProbabilityMeasure (positionGibbs U):=a.gibbs_isProbabilityMeasure
  let :IsProbabilityMeasure (phaseGibbs U):=by unfold phaseGibbs; infer_instance
  have hM:1≤(warmL2 ν (phaseGibbs U)).toReal:=by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono hW (one_le_warmL2 ν (phaseGibbs U) hac)
  have hD:1≤(Module.finrank ℝ E:ℝ)+Real.log ((warmL2 ν (phaseGibbs U)).toReal/ε):=
    (main_radius_bounds (Module.finrank ℝ E) hd hM hε hε1).1
  have hκ:1≤L/m:=(le_div_iff₀ a.m_pos).mpr (by simpa using a.m_le_L)
  have hlH:0≤LH/m^(3/2:ℝ):=div_nonneg (a2.constant_nonneg_of_dimension hd)
    (Real.rpow_nonneg a.m_pos.le _)
  exact ⟨div_pos (main_step_bounds hκ hlH hD).1 (Real.sqrt_pos.mpr a.m_pos),
    Nat.le_add_left 1 _,samplingEpochs_pos hε hε1⟩

end PersistencePays
#print axioms PersistencePays.A1.theorem_one_parameter_validity
#print axioms PersistencePays.A1.theorem_one_normalized
#print axioms PersistencePays.A1.theorem_one_kernel
#print axioms PersistencePays.A1.theorem_one
