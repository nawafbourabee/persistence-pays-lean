import PersistencePays.LinearPullbackBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Joint first/second derivatives of a time-dependent coefficient applied to position
have at most linear spatial growth. -/
noncomputable section
namespace PersistencePays
variable {E F V:Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem affine_time_derivative_bounds (B:F→L[ℝ]E→L[ℝ]V)
    {f:ℝ→F} (hf:ContDiff ℝ 2 f) (p:ℝ×E) {C:ℝ} (hC:0≤C)
    (h0:‖f p.1‖≤C) (h1:‖fderiv ℝ f p.1‖≤C)
    (h2:‖fderiv ℝ (fderiv ℝ f) p.1‖≤C) :
    ‖fderiv ℝ (fun q:ℝ×E=>B (f q.1) q.2) p‖≤‖B‖*C*(1+‖p.2‖) ∧
    ‖fderiv ℝ (fderiv ℝ (fun q:ℝ×E=>B (f q.1) q.2)) p‖≤2*‖B‖*C*(1+‖p.2‖) := by
  let l:ℝ×E→L[ℝ]ℝ:=ContinuousLinearMap.fst ℝ ℝ E
  let r:ℝ×E→L[ℝ]E:=ContinuousLinearMap.snd ℝ ℝ E
  let F₀:ℝ×E→F:=fun q=>f q.1
  have hfd:Differentiable ℝ f:=hf.differentiable (by norm_num)
  have hfdd:Differentiable ℝ (fderiv ℝ f):=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hF:ContDiff ℝ 2 F₀:=hf.comp contDiff_fst
  have hFd:Differentiable ℝ F₀:=hF.differentiable (by norm_num)
  have hFdd:Differentiable ℝ (fderiv ℝ F₀):=
    (hF.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have b1:‖fderiv ℝ F₀ p‖≤C := by
    calc
      _ ≤ ‖fderiv ℝ f p.1‖*‖l‖:=fderiv_linear_pullback_norm l (hfd _)
      _ ≤ C*1:=mul_le_mul h1 (ContinuousLinearMap.norm_fst_le ..) (norm_nonneg _) hC
      _ = C:=mul_one _
  have b2:‖fderiv ℝ (fderiv ℝ F₀) p‖≤C := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) p.1‖*‖l‖^2:=second_fderiv_linear_pullback_norm l hfd (hfdd _)
      _ ≤ C*1:=mul_le_mul h2 (by simpa using pow_le_pow_left₀ (norm_nonneg l) (ContinuousLinearMap.norm_fst_le (𝕜:=ℝ) (E:=ℝ) (F:=E)) 2) (by positivity) hC
      _ = C:=mul_one _
  constructor
  · have hn:=bilinear_fderiv_norm_bound B (hFd p) r.differentiableAt
    rw [r.fderiv] at hn
    calc
      _ ≤ ‖B‖*(‖f p.1‖*‖r‖+‖fderiv ℝ F₀ p‖*‖p.2‖):=hn
      _ ≤ ‖B‖*(C*1+C*‖p.2‖):=by
        gcongr
        exact ContinuousLinearMap.norm_snd_le ..
      _ = _:=by ring
  · have hn:=bilinear_second_linear_norm_bound B r hFd (hFdd p)
    calc
      _ ≤ ‖B‖*(2*‖fderiv ℝ F₀ p‖*‖r‖+‖fderiv ℝ (fderiv ℝ F₀) p‖*‖p.2‖):=hn
      _ ≤ ‖B‖*(2*C*1+C*‖p.2‖):=by
        gcongr
        exact ContinuousLinearMap.norm_snd_le ..
      _ ≤ _:=by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg B) hC) (norm_nonneg p.2)]

theorem time_only_derivative_bounds {f:ℝ→V} (hf:ContDiff ℝ 2 f)
    (p:ℝ×E) {C:ℝ} (hC:0≤C)
    (h1:‖fderiv ℝ f p.1‖≤C) (h2:‖fderiv ℝ (fderiv ℝ f) p.1‖≤C) :
    ‖fderiv ℝ (fun q:ℝ×E=>f q.1) p‖≤C ∧
    ‖fderiv ℝ (fderiv ℝ (fun q:ℝ×E=>f q.1)) p‖≤C := by
  let l:ℝ×E→L[ℝ]ℝ:=ContinuousLinearMap.fst ℝ ℝ E
  have hfd:Differentiable ℝ f:=hf.differentiable (by norm_num)
  have hfdd:Differentiable ℝ (fderiv ℝ f):=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  constructor
  · exact (fderiv_linear_pullback_norm l (hfd _)).trans (by
      calc
        _ ≤ C*1:=mul_le_mul h1 (ContinuousLinearMap.norm_fst_le ..) (norm_nonneg _) hC
        _ = C:=mul_one _)
  · exact (second_fderiv_linear_pullback_norm l hfd (hfdd _)).trans (by
      calc
        _ ≤ C*1:=mul_le_mul h2 (by simpa using pow_le_pow_left₀ (norm_nonneg l) (ContinuousLinearMap.norm_fst_le (𝕜:=ℝ) (E:=ℝ) (F:=E)) 2) (by positivity) hC
        _ = C:=mul_one _)

theorem affine_time_add_derivative_bounds (B:F→L[ℝ]E→L[ℝ]V)
    {f:ℝ→F} {k:ℝ→V} (hf:ContDiff ℝ 2 f) (hk:ContDiff ℝ 2 k)
    (p:ℝ×E) {C D:ℝ} (hC:0≤C) (hD:0≤D)
    (h0:‖f p.1‖≤C) (h1:‖fderiv ℝ f p.1‖≤C)
    (h2:‖fderiv ℝ (fderiv ℝ f) p.1‖≤C)
    (hk1:‖fderiv ℝ k p.1‖≤D) (hk2:‖fderiv ℝ (fderiv ℝ k) p.1‖≤D) :
    ‖fderiv ℝ (fun q:ℝ×E=>B (f q.1) q.2+k q.1) p‖≤(2*‖B‖*C+D)*(1+‖p.2‖) ∧
    ‖fderiv ℝ (fderiv ℝ (fun q:ℝ×E=>B (f q.1) q.2+k q.1)) p‖≤(2*‖B‖*C+D)*(1+‖p.2‖) := by
  let H:ℝ×E→V:=fun q=>B (f q.1) q.2
  let K:ℝ×E→V:=fun q=>k q.1
  have hH:ContDiff ℝ 2 H:=B.isBoundedBilinearMap.contDiff.comp ((hf.comp contDiff_fst).prodMk contDiff_snd)
  have hK:ContDiff ℝ 2 K:=hk.comp contDiff_fst
  have hdH:Differentiable ℝ H:=hH.differentiable (by norm_num)
  have hdK:Differentiable ℝ K:=hK.differentiable (by norm_num)
  have hdDH:Differentiable ℝ (fderiv ℝ H):=(hH.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hdDK:Differentiable ℝ (fderiv ℝ K):=(hK.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have bH:=affine_time_derivative_bounds B hf p hC h0 h1 h2
  have bK:=time_only_derivative_bounds hk p hD hk1 hk2
  have heq:fderiv ℝ (H+K)=fderiv ℝ H+fderiv ℝ K:=by
    funext x
    exact fderiv_add (hdH x) (hdK x)
  constructor
  · change ‖fderiv ℝ (H+K) p‖≤_
    rw [fderiv_add (hdH p) (hdK p)]
    calc
      _ ≤ ‖fderiv ℝ H p‖+‖fderiv ℝ K p‖:=norm_add_le _ _
      _ ≤ ‖B‖*C*(1+‖p.2‖)+D:=add_le_add bH.1 bK.1
      _ ≤ _:=by nlinarith [mul_nonneg (norm_nonneg B) hC, mul_nonneg (mul_nonneg (norm_nonneg B) hC) (norm_nonneg p.2),mul_nonneg hD (norm_nonneg p.2)]
  · change ‖fderiv ℝ (fderiv ℝ (H+K)) p‖≤_
    rw [heq,fderiv_add (hdDH p) (hdDK p)]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ H) p‖+‖fderiv ℝ (fderiv ℝ K) p‖:=by
        convert norm_add_le (fderiv ℝ (fderiv ℝ H) p) (fderiv ℝ (fderiv ℝ K) p) using 1
      _ ≤ 2*‖B‖*C*(1+‖p.2‖)+D:=add_le_add bH.2 bK.2
      _ ≤ _:=by nlinarith [mul_nonneg hD (norm_nonneg p.2)]

end PersistencePays
#print axioms PersistencePays.affine_time_derivative_bounds
