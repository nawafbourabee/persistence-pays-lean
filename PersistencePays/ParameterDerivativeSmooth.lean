import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual parameter derivatives remain jointly smooth, including in a latent parameter. -/
noncomputable section
namespace PersistencePays
variable {P Y V:Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem parameter_fderiv_contDiff {n:ℕ} {H:P×Y→V}
    (hH:ContDiff ℝ (n+1) H) :
    ContDiff ℝ n (fun q:P×Y=>fderiv ℝ (fun p=>H (p,q.2)) q.1) := by
  let F:(P×Y)→P→V:=fun q p=>H (p,q.2)
  have hf:ContDiff ℝ (n+1) F.uncurry:=hH.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact hf.fderiv contDiff_fst (by simp)

theorem parameter_second_fderiv_contDiff {n:ℕ} {H:P×Y→V}
    (hH:ContDiff ℝ (n+2) H) :
    ContDiff ℝ n (fun q:P×Y=>fderiv ℝ (fderiv ℝ (fun p=>H (p,q.2))) q.1) := by
  have h1:ContDiff ℝ (n+1) (fun q:P×Y=>fderiv ℝ (fun p=>H (p,q.2)) q.1):=
    parameter_fderiv_contDiff (n:=n+1) (by convert hH using 1 <;> norm_num [Nat.cast_add,add_assoc])
  exact parameter_fderiv_contDiff h1
end PersistencePays
#print axioms PersistencePays.parameter_second_fderiv_contDiff
