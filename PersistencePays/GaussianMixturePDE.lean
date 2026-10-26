import PersistencePays.GaussianMixtureFields

/-! Continuity and momentum conservation for the actual compact Gaussian mixture. -/
noncomputable section
set_option maxHeartbeats 800000
namespace PersistencePays
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
universe u
variable {E Z:Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]

theorem gaussianFlight_continuity (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    deriv (fun t=>gaussianFlightDensity μ g ε t y) s+
      vectorDivergence (gaussianFlightFlux μ g ε s) y=0 := by
  have hn:ContDiff ℝ 1 (fun p:ℝ×(E×E)=>singleFlightDensity ε p.1 y p.2) :=
    (singleFlightDensity_contDiff 1 hε).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hJ:ContDiff ℝ 1 (fun p:E×(E×E)=>singleFlightFlux ε s p.1 p.2) :=
    (singleFlightFlux_contDiff 1 hε).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hi:=compact_latent_deriv_integrable μ g hg hn s
  have hj:Integrable (fun z=>vectorDivergence (fun y=>singleFlightFlux ε s y (g z)) y) μ := by
    apply hi.neg.congr
    filter_upwards with z
    exact neg_eq_of_add_eq_zero_right (singleFlight_continuity hε s y (g z))
  unfold gaussianFlightDensity gaussianFlightFlux
  rw [compact_mixture_deriv μ g hg hn,compact_mixture_vectorDivergence μ g hg hJ,
    ← integral_add hi hj]
  have he (z:Z):deriv (fun t=>singleFlightDensity ε t y (g z)) s+
      vectorDivergence (fun y=>singleFlightFlux ε s y (g z)) y=0 :=
    singleFlight_continuity hε s y (g z)
  simp_rw [he]
  simp

theorem gaussianFlight_momentum (μ:Measure Z) [IsFiniteMeasure μ]
    (g:Z→E×E) (hg:Continuous g) {ε:ℝ} (hε:ε≠0) (s:ℝ) (y:E) :
    deriv (fun t=>gaussianFlightFlux μ g ε t y) s+
      matrixDivergence (gaussianFlightSecondMoment μ g ε s) y=0 := by
  have hJ:ContDiff ℝ 1 (fun p:ℝ×(E×E)=>singleFlightFlux ε p.1 y p.2) :=
    (singleFlightFlux_contDiff 1 hε).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hproj:ContDiff ℝ 1 (fun p:E×(E×E)=>((s,p.1),p.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  have hM := (singleFlightMoment_contDiff (E:=E) 1 hε).comp hproj
  have hMD:=compact_mixture_matrixDivergence μ g hg hM y
  dsimp only [Function.comp_def] at hMD
  have hi:=compact_latent_deriv_integrable μ g hg hJ s
  have hj:Integrable (fun z=>matrixDivergence (fun y=>singleFlightMoment ε s y (g z)) y) μ := by
    apply hi.neg.congr
    filter_upwards with z
    exact neg_eq_of_add_eq_zero_right (singleFlight_momentum hε s y (g z))
  unfold gaussianFlightFlux gaussianFlightSecondMoment
  rw [compact_mixture_deriv μ g hg hJ,hMD,
    ← integral_add hi hj]
  have he (z:Z):deriv (fun t=>singleFlightFlux ε t y (g z)) s+
      matrixDivergence (fun y=>singleFlightMoment ε s y (g z)) y=0 :=
    singleFlight_momentum hε s y (g z)
  simp_rw [he]
  simp

end PersistencePays
#print axioms PersistencePays.gaussianFlight_continuity
#print axioms PersistencePays.gaussianFlight_momentum
