import PersistencePays.NormalizationLaws
import PersistencePays.EpochKernel

/-! Pathwise normalization of the actual adjusted OBABO chain, including its
carried exponential threshold, rejected steps, and both OU half-steps. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory OBABOPath
open scoped RealInnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem A1.normalized_gradient_at {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (x:E) :
    gradient a.normalizedPotential (a.normalizationPosition x)=
      (Real.sqrt m)⁻¹•gradient U x := by
  rw [a.normalizedPotential_gradient,←a.normalizationPosition_symm_apply,
    MeasurableEquiv.symm_apply_apply]

theorem A1.normalization_kick {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (h:ℝ) (z:E×E) :
    kick (gradient a.normalizedPotential) (Real.sqrt m*h) (a.normalizationState z)=
      a.normalizationState (kick (gradient U) h z) := by
  change (a.normalizationPosition z.1,z.2-(Real.sqrt m*h)•
    gradient a.normalizedPotential (a.normalizationPosition z.1))=
      (a.normalizationPosition z.1,z.2-h•gradient U z.1)
  rw [a.normalized_gradient_at,smul_smul]
  have hs:(Real.sqrt m*h)*(Real.sqrt m)⁻¹=h:=by
    field_simp [(Real.sqrt_pos.mpr a.m_pos).ne']
  rw [hs]

theorem A1.normalization_drift {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (h:ℝ) (z:E×E) :
    drift (Real.sqrt m*h) (a.normalizationState z)=a.normalizationState (drift h z) := by
  rw [a.normalizationState_apply,a.normalizationState_apply]
  apply Prod.ext
  · simp only [drift,Prod.fst]
    module
  · rfl

theorem A1.normalization_verlet {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (h:ℝ) (z:E×E) :
    verlet (gradient a.normalizedPotential) (Real.sqrt m*h) (a.normalizationState z)=
      a.normalizationState (verlet (gradient U) h z) := by
  simp only [verlet,show Real.sqrt m*h/2=Real.sqrt m*(h/2) by ring,
    a.normalization_kick,a.normalization_drift]

theorem A1.normalization_ou {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (r σ:ℝ) (ξ:E) (z:E×E) :
    ou r σ ξ (a.normalizationState z)=a.normalizationState (ou r σ ξ z) := rfl

theorem A1.normalization_flip {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (z:E×E) :
    velocityFlip (a.normalizationState z)=a.normalizationState (velocityFlip z) := rfl

theorem A1.normalization_energy {U:E→ℝ} {m L:ℝ} (a:A1 U m L) (z:E×E) :
    phaseEnergy a.normalizedPotential (a.normalizationState z)=phaseEnergy U z-U a.minimizer := by
  change a.normalizedPotential (a.normalizationPosition z.1)+_=_
  rw [A1.normalizedPotential,scaledPotential,←a.normalizationPosition_symm_apply,
    MeasurableEquiv.symm_apply_apply]
  change U z.1-U a.minimizer+inner ℝ z.2 z.2/2=
    (U z.1+inner ℝ z.2 z.2/2)-U a.minimizer
  ring

theorem A1.normalization_accepted {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (ξ ξ':ℕ→E) (k:ℕ) (z:E×E) :
    acceptedUpdate (gradient a.normalizedPotential) (Real.sqrt m*h) r σ ξ ξ' k
      (a.normalizationState z)=a.normalizationState (acceptedUpdate (gradient U) h r σ ξ ξ' k z) := by
  simp only [acceptedUpdate,a.normalization_ou,a.normalization_verlet]

theorem A1.normalization_rejected {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (r σ:ℝ) (ξ ξ':ℕ→E) (k:ℕ) (z:E×E) :
    rejectedUpdate r σ ξ ξ' k (a.normalizationState z)=
      a.normalizationState (rejectedUpdate r σ ξ ξ' k z) := rfl

theorem A1.normalization_defect {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (ξ:ℕ→E) (k:ℕ) (z:E×E) :
    energyDefect a.normalizedPotential (gradient a.normalizedPotential) (Real.sqrt m*h) r σ ξ k
      (a.normalizationState z)=energyDefect U (gradient U) h r σ ξ k z := by
  simp only [energyDefect,a.normalization_ou,a.normalization_verlet,a.normalization_energy]
  ring

lemma adjustedPath_conjugate {S T:Type*} (f:S→T)
    (A R:ℕ→S→S) (D:ℕ→S→ℝ) (A' R':ℕ→T→T) (D':ℕ→T→ℝ)
    (hA:∀k x,A' k (f x)=f (A k x)) (hR:∀k x,R' k (f x)=f (R k x))
    (hD:∀k x,D' k (f x)=D k x) (z:S) (ell:ℝ) (n:ℕ) :
    EpochAcceptance.adjustedPath A' R' D' (f z) ell n=
      (f (EpochAcceptance.adjustedPath A R D z ell n).1,
        (EpochAcceptance.adjustedPath A R D z ell n).2) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [EpochAcceptance.adjustedPath,ih,Prod.fst,Prod.snd,hD]
    split_ifs <;> simp only [Prod.fst,Prod.snd,hA,hR]

theorem A1.normalization_actualPath {U:E→ℝ} {m L:ℝ} (a:A1 U m L)
    (h r σ:ℝ) (ξ ξ':ℕ→E) (z:E×E) (ell:ℝ) (n:ℕ) :
    actualPath a.normalizedPotential (gradient a.normalizedPotential) (Real.sqrt m*h) r σ ξ ξ'
      (a.normalizationState z) ell n=
    (a.normalizationState.prodCongr (MeasurableEquiv.refl ℝ))
      (actualPath U (gradient U) h r σ ξ ξ' z ell n) :=
  adjustedPath_conjugate a.normalizationState _ _ _ _ _ _
    (a.normalization_accepted h r σ ξ ξ') (a.normalization_rejected r σ ξ ξ')
    (a.normalization_defect h r σ ξ) z ell n

end PersistencePays
#print axioms PersistencePays.A1.normalization_actualPath
