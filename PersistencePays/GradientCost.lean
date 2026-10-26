import PersistencePays.OBABOPath

/-!
# A cached implementation and its gradient-oracle cost

`queryGradient` is the only operation which evaluates the supplied gradient
oracle, and increments its counter once. Initialization makes one query;
every attempted step makes exactly one query at its proposed position,
including a proposal which is rejected. The cached implementation is proved
equal to Definition 2.2, and its cache is proved valid after either branch.
-/

namespace PersistencePays.CachedOBABO

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure State (E : Type*) where
  phase : E × E
  cachedGradient : E
  threshold : ℝ
  calls : ℕ

/-- Gradient-oracle operation, including its exact evaluation count. -/
def queryGradient (g : E → E) (x : E) (calls : ℕ) : E × ℕ :=
  (g x, calls + 1)

def initializeCache (g : E → E) (z : E × E) (ell : ℝ) : State E :=
  let queried := queryGradient g z.1 0
  ⟨z, queried.1, ell, queried.2⟩

def projection (s : State E) : (E × E) × ℝ := (s.phase, s.threshold)

def Consistent (g : E → E) (s : State E) : Prop :=
  s.cachedGradient = g s.phase.1

/-- Complete an attempt after the sole new gradient query has returned. -/
def completeAttempt (r σ : ℝ) (ξ' : E) (s : State E)
    (wv x1 v1 g1 : E) (delta : ℝ) (calls : ℕ) : State E :=
  if delta < s.threshold then
    ⟨(x1, r • v1 + σ • ξ'), g1, s.threshold - delta, calls⟩
  else
    ⟨(s.phase.1, r • (-wv) + σ • ξ'), s.cachedGradient, s.threshold, calls⟩

theorem completeAttempt_consistent (g : E → E) (r σ : ℝ) (ξ' : E) (s : State E)
    (wv x1 v1 g1 : E) (delta : ℝ) (calls : ℕ)
    (hc : Consistent g s) (hg1 : g1 = g x1) :
    Consistent g (completeAttempt r σ ξ' s wv x1 v1 g1 delta calls) := by
  unfold completeAttempt
  split_ifs
  · exact hg1
  · exact hc

theorem completeAttempt_calls (r σ : ℝ) (ξ' : E) (s : State E)
    (wv x1 v1 g1 : E) (delta : ℝ) (calls : ℕ) :
    (completeAttempt r σ ξ' s wv x1 v1 g1 delta calls).calls = calls := by
  unfold completeAttempt
  split_ifs <;> rfl

theorem completeAttempt_projection (r σ : ℝ) (ξ' : E) (s : State E)
    (wv x1 v1 g1 : E) (delta : ℝ) (calls : ℕ) :
    projection (completeAttempt r σ ξ' s wv x1 v1 g1 delta calls) =
      if delta < s.threshold then ((x1, r • v1 + σ • ξ'), s.threshold - delta)
      else ((s.phase.1, r • (-wv) + σ • ξ'), s.threshold) := by
  unfold completeAttempt
  split_ifs <;> rfl

/-- Exactly one new gradient query occurs, before either acceptance branch. -/
def attempt (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : E) (s : State E) : State E :=
  let wv := r • s.phase.2 + σ • ξ
  let V := wv - (h / 2) • s.cachedGradient
  let x1 := s.phase.1 + h • V
  let queried := queryGradient g x1 s.calls
  let v1 := V - (h / 2) • queried.1
  let delta := U x1 + ⟪v1, v1⟫_ℝ / 2 - (U s.phase.1 + ⟪wv, wv⟫_ℝ / 2)
  completeAttempt r σ ξ' s wv x1 v1 queried.1 delta queried.2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem initialize_consistent (g : E → E) (z : E × E) (ell : ℝ) :
    Consistent g (initializeCache g z ell) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem initialize_calls (g : E → E) (z : E × E) (ell : ℝ) :
    (initializeCache g z ell).calls = 1 := rfl

theorem attempt_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : E) (s : State E) (hc : Consistent g s) :
    Consistent g (attempt U g h r σ ξ ξ' s) := by
  exact completeAttempt_consistent g r σ ξ' s _ _ _ _ _ _ hc rfl

theorem attempt_calls (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : E) (s : State E) :
    (attempt U g h r σ ξ ξ' s).calls = s.calls + 1 := by
  exact completeAttempt_calls r σ ξ' s _ _ _ _ _ _

/-- The cache produces exactly the adjusted OBABO state and threshold. -/
theorem attempt_projection (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (k : ℕ) (s : State E) (hc : Consistent g s) :
    projection (attempt U g h r σ (ξ k) (ξ' k) s) =
      if OBABOPath.energyDefect U g h r σ ξ k s.phase < s.threshold then
        (OBABOPath.acceptedUpdate g h r σ ξ ξ' k s.phase,
          s.threshold - OBABOPath.energyDefect U g h r σ ξ k s.phase)
      else (OBABOPath.rejectedUpdate r σ ξ ξ' k s.phase, s.threshold) := by
  have hc' : s.cachedGradient = g s.phase.1 := hc
  dsimp only [attempt]
  rw [completeAttempt_projection]
  rw [hc']
  rfl

def runSteps (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (s : State E) : ℕ → State E
  | 0 => s
  | n + 1 => attempt U g h r σ (ξ n) (ξ' n) (runSteps U g h r σ ξ ξ' s n)

theorem runSteps_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (s : State E) (hc : Consistent g s) (n : ℕ) :
    Consistent g (runSteps U g h r σ ξ ξ' s n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact attempt_consistent U g h r σ (ξ n) (ξ' n) _ ih

theorem runSteps_calls (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (s : State E) (n : ℕ) :
    (runSteps U g h r σ ξ ξ' s n).calls = s.calls + n := by
  induction n with
  | zero => simp [runSteps]
  | succ n ih => rw [runSteps, attempt_calls, ih]; omega

theorem runSteps_projection (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → E) (s : State E) (hc : Consistent g s) (n : ℕ) :
    projection (runSteps U g h r σ ξ ξ' s n) =
      OBABOPath.actualPath U g h r σ ξ ξ' s.phase s.threshold n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runSteps, attempt_projection U g h r σ ξ ξ' n _
        (runSteps_consistent U g h r σ ξ ξ' s hc n)]
      have hp := congrArg Prod.fst ih
      have ht := congrArg Prod.snd ih
      change (runSteps U g h r σ ξ ξ' s n).phase = _ at hp
      change (runSteps U g h r σ ξ ξ' s n).threshold = _ at ht
      rw [hp, ht]
      rfl

/-- Drawing a new epoch threshold makes no gradient query. -/
def refreshThreshold (s : State E) (ell : ℝ) : State E :=
  { s with threshold := ell }

def runEpochs (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → ℕ → E) (ell : ℕ → ℝ) (stepsPerEpoch : ℕ)
    (s : State E) : ℕ → State E
  | 0 => s
  | n + 1 => runSteps U g h r σ (ξ n) (ξ' n)
      (refreshThreshold (runEpochs U g h r σ ξ ξ' ell stepsPerEpoch s n) (ell n))
      stepsPerEpoch

theorem runEpochs_consistent (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → ℕ → E) (ell : ℕ → ℝ) (stepsPerEpoch : ℕ)
    (s : State E) (hc : Consistent g s) (n : ℕ) :
    Consistent g (runEpochs U g h r σ ξ ξ' ell stepsPerEpoch s n) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
      apply runSteps_consistent
      exact ih

theorem runEpochs_calls (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → ℕ → E) (ell : ℕ → ℝ) (stepsPerEpoch : ℕ)
    (s : State E) (n : ℕ) :
    (runEpochs U g h r σ ξ ξ' ell stepsPerEpoch s n).calls =
      s.calls + n * stepsPerEpoch := by
  induction n with
  | zero => simp [runEpochs]
  | succ n ih =>
      rw [runEpochs, runSteps_calls]
      change (runEpochs U g h r σ ξ ξ' ell stepsPerEpoch s n).calls + stepsPerEpoch = _
      rw [ih, Nat.succ_mul]
      omega

/-- Exactly `N * E + 1` gradient-oracle queries, with rejected proposals counted. -/
theorem total_gradient_queries (U : E → ℝ) (g : E → E) (h r σ : ℝ)
    (ξ ξ' : ℕ → ℕ → E) (ell : ℕ → ℝ) (stepsPerEpoch epochs : ℕ) (z : E × E) :
    (runEpochs U g h r σ ξ ξ' ell stepsPerEpoch (initializeCache g z 0) epochs).calls =
      epochs * stepsPerEpoch + 1 := by
  rw [runEpochs_calls, initialize_calls]
  omega

end

end PersistencePays.CachedOBABO
