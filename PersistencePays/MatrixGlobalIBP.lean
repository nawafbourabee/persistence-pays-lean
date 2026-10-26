import PersistencePays.MatrixCutoff

/-! Ordinary matrix integration by parts after removal of radial cutoffs.
The identity-vector specialization supplies the nonsingular identity term in
the signed displacement inequality. -/
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology RealInnerProductSpace ContDiff
namespace PersistencePays.QuadraticTransport
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma radialCutoff_integral_tendsto {μ : Measure E} {f:E→ℝ} (hf:Integrable f μ) :
    Tendsto (fun n => ∫ x,radialCutoff n x*f x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => (radialCutoff_contDiff n).continuous.aestronglyMeasurable.mul
      hf.aestronglyMeasurable) hf.norm
  · intro n
    filter_upwards with x
    change ‖radialCutoff n x*f x‖≤‖f x‖
    rw [norm_mul,Real.norm_of_nonneg (radialCutoff_mem_Icc n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_mem_Icc n x).2
  · filter_upwards with x
    simpa only [Pi.mul_apply,one_mul] using (radialCutoff_tendsto x).mul_const (f x)

theorem global_matrix_ibp {S:E→E→L[ℝ]E} {T:E→E}
    (hS:ContDiff ℝ 1 S) (hT:ContDiff ℝ 1 T)
    (hsym:∀ x,(S x).toLinearMap.IsSymmetric)
    (hST:Integrable (fun x => S x (T x)) volume)
    (hdiv:Integrable (fun x => ⟪matrixDivergence S x,T x⟫) volume)
    (htrace:Integrable (fun x => ((S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E) volume) :
    (∫ x,((S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E)=
      -∫ x,⟪matrixDivergence S x,T x⟫ := by
  let q : E → ℝ := fun x => ((S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E
  have hlocal (n:ℕ) : (∫ x,radialCutoff n x*q x)=
      -(∫ x,radialCutoff n x*⟪matrixDivergence S x,T x⟫)-
        ∫ x,(fderiv ℝ (radialCutoff n) x) (S x (T x)) := by
    have hχ := (radialCutoff_contDiff (E:=E) n).of_le (show (1:ℕ∞)≤∞ by simp)
    have hh := (compact_matrix_ibp (hχ.smul hS) ((radialCutoff_compact n).smul_right) hT
      (fun x => (hsym x).smul (by simp))).2.2
    change (∫ x,((radialCutoff n x • S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E)=
      -∫ x,⟪matrixDivergence (fun y => radialCutoff n y • S y) x,T x⟫ at hh
    have heq (x:E) :
        ((radialCutoff n x • S x).comp (fderiv ℝ T x)).toLinearMap.trace ℝ E =
          radialCutoff n x*q x := by
      simp only [smul_comp,toLinearMap_smul,map_smul,smul_eq_mul,q]
    simp only [heq,matrixDivergence_smul_pairing hχ hS hsym] at hh
    rw [integral_add (radialCutoff_mul_integrable hdiv n)
      (radialCutoff_derivative_integrable hST n)] at hh
    simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hh
  have hleft := radialCutoff_integral_tendsto htrace
  have hright := (radialCutoff_integral_tendsto hdiv).neg.sub
    (radialCutoff_derivative_error hST)
  have he : (fun n => ∫ x,radialCutoff n x*q x) =
      (fun n => -(∫ x,radialCutoff n x*⟪matrixDivergence S x,T x⟫)-
        ∫ x,(fderiv ℝ (radialCutoff n) x) (S x (T x))) := funext hlocal
  change Tendsto (fun n => ∫ x,radialCutoff n x*q x) atTop _ at hleft
  rw [he] at hleft
  simpa only [sub_zero] using tendsto_nhds_unique hleft hright

theorem identity_matrix_ibp {S:E→E→L[ℝ]E}
    (hS:ContDiff ℝ 1 S) (hsym:∀ x,(S x).toLinearMap.IsSymmetric)
    (hSx:Integrable (fun x => S x x) volume)
    (hdiv:Integrable (fun x => ⟪matrixDivergence S x,x⟫) volume)
    (htrace:Integrable (fun x => (S x).toLinearMap.trace ℝ E) volume) :
    (∫ x,(S x).toLinearMap.trace ℝ E) = -∫ x,⟪matrixDivergence S x,x⟫ := by
  simpa only [fderiv_id,comp_id,id_eq] using
    global_matrix_ibp hS (contDiff_id (n:=1)) hsym hSx hdiv
      (by simpa only [fderiv_id,comp_id] using htrace)

end
end PersistencePays.QuadraticTransport
#print axioms PersistencePays.QuadraticTransport.global_matrix_ibp
