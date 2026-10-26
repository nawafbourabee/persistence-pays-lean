import PersistencePays.MainStepBounds
import PersistencePays.WarmEpochCount
import PersistencePays.ComplexityPowerBounds

/-! An explicit absolute-constant bound for the entire numerical gradient
budget, including the actual integer epoch lengths and epoch count. -/
noncomputable section
namespace PersistencePays.OBABOPath

theorem main_gradient_complexity {L LH D ε:ℝ}
    (hL:1≤L) (hLH:0≤LH) (hD:1≤D) (hε:0<ε) (hε1:ε≤1) :
    (samplingEpochs ε:ℝ)*((mainEpochPredecessor L LH D+1:ℕ):ℝ)≤
      (10:ℝ)^30*(mainLogScale L LH D)^(3/2:ℝ)*
        (Real.sqrt (L*D)+Real.sqrt LH*D^(3/4:ℝ))*Real.log (2/ε) := by
  let Λ:=mainLogScale L LH D
  let S:=mainComplexityScale L LH D
  let h:=mainStep L LH D
  have hΛ:1≤Λ:=(main_log_bounds hL hLH hD).1
  have hS:1≤S:=(main_log_bounds hL hLH hD).2.2.1
  have hΛ0:0<Λ:=by linarith
  have hS0:0<S:=by linarith
  have hh:0<h:=(main_step_bounds hL hLH hD).1
  have hhmax:h≤1:=by
    have hh':= (main_step_bounds hL hLH hD).2.1
    change h≤1/(10:ℝ)^20 at hh'
    linarith
  have hratio:1≤Λ/h:=(le_div_iff₀ hh).mpr (by linarith)
  have hceil:((mainEpochPredecessor L LH D+1:ℕ):ℝ)≤(10:ℝ)^8*(Λ/h):=by
    have hc:=(Nat.ceil_lt_add_one (show 0≤(10:ℝ)^7*Λ/h by positivity)).le
    change (mainEpochPredecessor L LH D:ℝ)≤(10:ℝ)^7*Λ/h+1 at hc
    rw [Nat.cast_add,Nat.cast_one]
    rw [mul_div_assoc] at hc
    norm_num at hc ⊢
    nlinarith only [hc,hratio]
  have hlog:0<Real.log (2/ε):=Real.log_pos ((one_lt_div hε).mpr (by linarith))
  have hN:(samplingEpochs ε:ℝ)≤3*Real.log (2/ε):=by
    apply (samplingEpochs_bound hε hε1).trans
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<4))).mpr
      (by nlinarith [log_four_ge_one])
  have hratioeq:Λ/h=(10:ℝ)^20*(Λ^(3/2:ℝ)*Real.sqrt S):=by
    change Λ/(1/((10:ℝ)^20*Real.sqrt Λ*Real.sqrt S))=_
    rw [div_div_eq_mul_div,div_one]
    rw [←sqrt_lambda_mul_lambda hΛ0.le]
    ring
  have hSbound:Real.sqrt S≤Real.sqrt (L*D)+Real.sqrt LH*D^(3/4:ℝ):=
    sqrt_mixed_complexity (by linarith) hLH (by linarith)
  calc
    _≤(3*Real.log (2/ε))*((10:ℝ)^8*(Λ/h)):=
      mul_le_mul hN hceil (Nat.cast_nonneg _) (by positivity)
    _= (3*(10:ℝ)^28)*Λ^(3/2:ℝ)*Real.sqrt S*Real.log (2/ε):=by rw [hratioeq];ring
    _≤(10:ℝ)^30*Λ^(3/2:ℝ)*Real.sqrt S*Real.log (2/ε):=by
      gcongr
      norm_num
    _≤(10:ℝ)^30*Λ^(3/2:ℝ)*(Real.sqrt (L*D)+Real.sqrt LH*D^(3/4:ℝ))*Real.log (2/ε):=by
      gcongr
    _=_:=rfl

end PersistencePays.OBABOPath
#print axioms PersistencePays.OBABOPath.main_gradient_complexity
