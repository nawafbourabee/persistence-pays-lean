import PersistencePays.FlowDensityTransport
import PersistencePays.FlowTaylor

/-! Signed relative trajectories and exact density transport between any two
points of one classical flow interval, including backwards time. -/
noncomputable section
namespace PersistencePays
open MeasureTheory Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma add_mem_interval_of_relative {a b s t u:ℝ} (hs:s∈Icc a b) (ht:t∈Icc a b)
    (hu:u∈uIcc 0 (t-s)) : s+u∈Icc a b := by
  rcases mem_uIcc.mp hu with h|h <;> constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]

theorem VariationalFlow.relative_density_trajectory (μ:Measure E) [μ.IsAddHaarMeasure]
    {m:ℝ→E→E} {Dm:ℝ→E→E→L[ℝ]E} {a b:ℝ}
    (flow:VariationalFlow E m Dm a b) (hab:a≤b)
    (n:ℝ×E→ℝ) (hn:∀t∈Icc a b,∀x,DifferentiableAt ℝ n (t,x))
    (hpos:∀t∈Icc a b,∀x,0<n (t,x))
    (hpde:∀t∈Icc a b,∀x,fderiv ℝ n (t,x) (1,m t x)=
      -n (t,x)*LinearMap.trace ℝ E (Dm t x).toLinearMap)
    {s t:ℝ} (hs:s∈Icc a b) (ht:t∈Icc a b) :
    ∃X:ℝ→E→E,(∀x,X 0 x=x) ∧
      (∀u∈uIcc 0 (t-s),Measurable (X u)) ∧
      (∀x,∀u∈uIcc 0 (t-s),HasDerivWithinAt (fun v=>X v x)
        (m (s+u) (X u x)) (uIcc 0 (t-s)) u) ∧
      (μ.withDensity (fun x=>ENNReal.ofReal (n (s,x)))).map (X (t-s))=
        μ.withDensity (fun x=>ENNReal.ofReal (n (t,x))) := by
  obtain ⟨g,hg,hleft,hright⟩:=flow.exists_measurable_inverse hs
  let X:ℝ→E→E:=fun u x=>flow.toFun (s+u) (g x)
  have hfm (v:ℝ) (hv:v∈Icc a b):Measurable (flow.toFun v):=
    (continuous_iff_continuousAt.mpr (fun x=>(flow.spatial_derivative v hv x).continuousAt)).measurable
  have hmaps:MapsTo (fun u=>s+u) (uIcc 0 (t-s)) (Icc a b):=
    fun u hu=>add_mem_interval_of_relative hs ht hu
  refine ⟨X,?_,?_,?_,?_⟩
  · intro x
    simpa only [X,add_zero] using hright x
  · intro u hu
    exact (hfm (s+u) (hmaps hu)).comp hg
  · intro x u hu
    have hh:HasDerivWithinAt (fun v=>flow.toFun v (g x))
        (m (s+u) (flow.toFun (s+u) (g x))) (Icc a b) (s+u):=
      flow.time_derivative (s+u) (hmaps hu) (g x)
    have hc:=hh.scomp u ((hasDerivWithinAt_id u (uIcc 0 (t-s))).const_add s) hmaps
    change HasDerivWithinAt (fun v=>X v x) (1 • m (s+u) (X u x)) (uIcc 0 (t-s)) u at hc
    simpa only [one_smul] using hc
  · have hback:=flow.transports_density_inverse μ hab n hn hpos hpde hs hg hleft
    have hforward:=flow.transports_density μ hab n hn hpos hpde ht
    have he:X (t-s)=flow.toFun t ∘ g:=by funext x; simp [X]
    rw [he,←Measure.map_map (hfm t ht) hg,hback,hforward]

end PersistencePays
#print axioms PersistencePays.VariationalFlow.relative_density_trajectory
