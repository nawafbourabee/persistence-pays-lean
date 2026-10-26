import PersistencePays.AdditiveNoiseApproximation

/-! Quantitative quadratic-moment continuity of additive Gaussian (or other
finite-second-moment) regularization, valid also for the max norm on phase space. -/
noncomputable section
namespace PersistencePays
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]

theorem abs_norm_sq_add_smul_sub_le (x y : S) (ε : ℝ) :
    |‖x+ε•y‖^2-‖x‖^2| ≤ |ε| *(‖x‖^2+(1+|ε|)*‖y‖^2) := by
  have hn : ‖x+ε•y‖ ≤ ‖x‖+|ε| *‖y‖ := by
    simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le x (ε•y)
  have hd : |‖x+ε•y‖-‖x‖| ≤ |ε| *‖y‖ := by
    simpa only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using abs_norm_sub_norm_le (x+ε•y) x
  have hmul := mul_le_mul hd (show ‖x+ε•y‖+‖x‖ ≤ 2*‖x‖+|ε| *‖y‖ by linarith)
    (by positivity : 0 ≤ ‖x+ε•y‖+‖x‖) (by positivity : 0 ≤ |ε| *‖y‖)
  have he : |‖x+ε•y‖^2-‖x‖^2| = |‖x+ε•y‖-‖x‖| *(‖x+ε•y‖+‖x‖) := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ‖x+ε•y‖+‖x‖)]
    ring
  rw [he]
  have hs := mul_nonneg (abs_nonneg ε) (sq_nonneg (‖x‖-‖y‖))
  nlinarith

theorem additiveNoise_moment_difference (μ γ : ProbabilityMeasure S) (ε : ℝ)
    (hμ : MemLp id 2 (μ : Measure S)) (hγ : MemLp id 2 (γ : Measure S)) :
    |(∫ x, ‖x‖^2 ∂(additiveNoiseProbability μ γ ε : Measure S))-
      (∫ x, ‖x‖^2 ∂(μ : Measure S))| ≤
        |ε| *((∫ x, ‖x‖^2 ∂(μ : Measure S))+
          (1+|ε|)*(∫ x, ‖x‖^2 ∂(γ : Measure S))) := by
  let ρ := (μ : Measure S).prod (γ : Measure S)
  have h1 : Integrable (fun z : S×S => ‖z.1‖^2) ρ :=
    (hμ.comp_fst (γ : Measure S)).norm.integrable_sq
  have h2 : Integrable (fun z : S×S => ‖z.2‖^2) ρ :=
    (hγ.comp_snd (μ : Measure S)).norm.integrable_sq
  have hsum : Integrable (fun z : S×S => ‖z.1+ε•z.2‖^2) ρ :=
    ((hμ.comp_fst (γ : Measure S)).add
      ((hγ.comp_snd (μ : Measure S)).const_smul ε)).norm.integrable_sq
  have he1 : (∫ x, ‖x‖^2 ∂(additiveNoiseProbability μ γ ε : Measure S)) =
      ∫ z : S×S, ‖z.1+ε•z.2‖^2 ∂ρ := integral_map (by fun_prop) (by fun_prop)
  have he2 : (∫ x, ‖x‖^2 ∂(μ : Measure S)) = ∫ z : S×S, ‖z.1‖^2 ∂ρ := by
    rw [integral_fun_fst (fun x : S => ‖x‖^2),probReal_univ,one_smul]
  rw [he1,he2,← integral_sub hsum h1]
  calc
    _ ≤ ∫ z : S×S, |‖z.1+ε•z.2‖^2-‖z.1‖^2| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ z : S×S, |ε| *(‖z.1‖^2+(1+|ε|)*‖z.2‖^2) ∂ρ := by
      apply integral_mono (hsum.sub h1).abs ((h1.add (h2.const_mul _)).const_mul _)
      intro z
      exact abs_norm_sq_add_smul_sub_le z.1 z.2 ε
    _ = _ := by
      have hb : Integrable (fun z : S×S => ‖z.1‖^2+(1+|ε|)*‖z.2‖^2) ρ :=
        h1.add (h2.const_mul _)
      rw [integral_const_mul, integral_add h1 (h2.const_mul _), integral_const_mul]
      rw [integral_fun_snd (fun x : S => ‖x‖^2),probReal_univ,one_smul]

theorem additiveNoise_moment_tendsto (μn : ℕ → ProbabilityMeasure S)
    (μ γ : ProbabilityMeasure S) (ε : ℕ → ℝ)
    (hμn : ∀ n, MemLp id 2 (μn n : Measure S))
    (hγ : MemLp id 2 (γ : Measure S)) (hε : Tendsto ε atTop (𝓝 0))
    (hm : Tendsto (fun n => ∫ x, ‖x‖^2 ∂(μn n : Measure S)) atTop
      (𝓝 (∫ x, ‖x‖^2 ∂(μ : Measure S)))) :
    Tendsto (fun n => ∫ x, ‖x‖^2 ∂(additiveNoiseProbability (μn n) γ (ε n) : Measure S))
      atTop (𝓝 (∫ x, ‖x‖^2 ∂(μ : Measure S))) := by
  have hεa : Tendsto (fun n => |ε n|) atTop (𝓝 0) := by simpa using hε.abs
  have hb := hεa.mul (hm.add (((tendsto_const_nhds (x := (1:ℝ))).add hεa).mul_const
    (∫ x, ‖x‖^2 ∂(γ : Measure S))))
  simp only [zero_mul] at hb
  have hzero : Tendsto (fun n =>
      (∫ x, ‖x‖^2 ∂(additiveNoiseProbability (μn n) γ (ε n) : Measure S))-
        (∫ x, ‖x‖^2 ∂(μn n : Measure S))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero (fun _ => abs_nonneg _) (fun n =>
      additiveNoise_moment_difference (μn n) γ (ε n) (hμn n) hγ) hb
  have hh := hzero.add hm
  simpa only [sub_add_cancel,zero_add] using hh

end PersistencePays
#print axioms PersistencePays.additiveNoise_moment_tendsto
