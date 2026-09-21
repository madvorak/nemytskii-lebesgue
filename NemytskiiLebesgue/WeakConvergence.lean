import NemytskiiLebesgue.Vitali

open MeasureTheory Filter
open scoped ENNReal Topology

def Function.WeaklyConvergesTo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (v : E) :
    Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n : ℕ => f (u n)) atTop (𝓝 (f v))

theorem Function.IsCaratheodory.stronglyConvergesTo_of_weaklyConvergesTo_of_unifIntegrable_of_growth
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : Ω → ℝ → ℝ} (hf : f.IsCaratheodory μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {ι : X →L[ℝ] (Ω → ℝ)} (hιp : ∀ x : X, MemLp (ι x) p μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q).toReal)
    {u : ℕ → X} (hup : UnifIntegrable (ι ∘ u) p μ)
    {v : X} (huv : u.WeaklyConvergesTo v) :
    (fun n : ℕ => fun ω : Ω => f ω (ι (u n) ω)).ConvergesTo (fun ω : Ω => f ω (ι v ω)) q μ := by
  convert
    hf.seqContinuous_nemytskii_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    .. using 1
  any_goals tauto
  · exact (MemLp.aestronglyMeasurable <| hιp <| u ·)
  · convert tendstoInMeasure_of_tendsto_ae (MemLp.aestronglyMeasurable <| hιp <| u ·) _
    apply Eventually.of_forall
    intro ω
    have := huv ((ContinuousLinearMap.proj ω).comp ι)
    aesop
