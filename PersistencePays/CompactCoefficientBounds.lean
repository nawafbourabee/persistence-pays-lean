import PersistencePays.ParameterDerivativeSmooth
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Uniform bounds for actual time derivatives over compact latent parameters. -/
noncomputable section
namespace PersistencePays
open Set
variable {Y V Z:Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace Z] [CompactSpace Z]
local instance compactCoefficientBoundsInst1 : NormedAddCommGroup (ℝ→L[ℝ]V) := inferInstance
local instance compactCoefficientBoundsInst2 : NormedAddCommGroup (ℝ→L[ℝ]ℝ→L[ℝ]V) := inferInstance

theorem compact_coefficient_c2_bounds {H:ℝ×Y→V} (hH:ContDiff ℝ 3 H)
    (g:Z→Y) (hg:Continuous g) (a b:ℝ) :
    ∃C:ℝ,0<C ∧ ∀s∈Icc a b,∀z,
      ‖H (s,g z)‖≤C ∧
      ‖fderiv ℝ (fun t=>H (t,g z)) s‖≤C ∧
      ‖fderiv ℝ (fderiv ℝ (fun t=>H (t,g z))) s‖≤C := by
  let D:ℝ×Y→ℝ→L[ℝ]V:=fun q=>fderiv ℝ (fun t=>H (t,q.2)) q.1
  let DD:ℝ×Y→ℝ→L[ℝ]ℝ→L[ℝ]V:=fun q=>fderiv ℝ (fderiv ℝ (fun t=>H (t,q.2))) q.1
  have hd:Continuous D:=(parameter_fderiv_contDiff (n:=2) (by convert hH using 1 <;> norm_num)).continuous
  have hdd:Continuous DD:=(parameter_second_fderiv_contDiff (n:=1) (by convert hH using 1 <;> norm_num)).continuous
  let φ:ℝ×Z→ℝ:=fun p=>‖H (p.1,g p.2)‖+‖D (p.1,g p.2)‖+‖DD (p.1,g p.2)‖
  have hp:Continuous (fun p:ℝ×Z=>(p.1,g p.2)):=continuous_fst.prodMk (hg.comp continuous_snd)
  have hddn:Continuous (fun p:ℝ×Z=>‖DD (p.1,g p.2)‖) := by
    convert Continuous.norm (hdd.comp hp) using 1
    rfl
  have hφ:Continuous φ:=((hH.continuous.comp hp).norm.add (hd.comp hp).norm).add hddn
  obtain ⟨C,hC,hbound⟩:=((isCompact_Icc.prod (isCompact_univ: IsCompact (univ:Set Z))).image hφ).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro s hs z
  have hn:φ (s,z)≤C:=le_trans (le_abs_self _) (hbound _ (mem_image_of_mem φ ⟨hs,mem_univ z⟩))
  change ‖H (s,g z)‖+‖D (s,g z)‖+‖DD (s,g z)‖≤C at hn
  exact ⟨by linarith [norm_nonneg (D (s,g z)),norm_nonneg (DD (s,g z))],
    by change ‖D (s,g z)‖≤C; linarith [norm_nonneg (H (s,g z)),norm_nonneg (DD (s,g z))],
    by change ‖DD (s,g z)‖≤C; linarith [norm_nonneg (H (s,g z)),norm_nonneg (D (s,g z))]⟩
end PersistencePays
#print axioms PersistencePays.compact_coefficient_c2_bounds
