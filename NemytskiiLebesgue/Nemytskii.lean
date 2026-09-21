import NemytskiiLebesgue.Continuity

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

theorem Function.IsCaratheodory.nonneg_integral_nemytskii_sub_nemytskii_inner_memLp_sub_memLp_of_monotone_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : f.IsCaratheodory μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : E, ⟪f ω s - f ω t, s - t⟫ ≥ 0)
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    0 ≤ ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ := by
  constructor
  · apply hpq.integrable_memLp_inner_memLp
    · apply MemLp.sub <;> apply hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC hfaCpq <;> assumption
    · exact MemLp.sub hup hvp
  · apply integral_nonneg_of_ae
    filter_upwards [hf0] with ω hω
    exact hω (u ω) (v ω)

theorem Function.IsCaratheodory.nonneg_integral_nemytskii_sub_nemytskii_mul_memLp_sub_memLp_of_monotone_of_growth_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ → ℝ} (hf : f.IsCaratheodory μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : ℝ, (f ω s - f ω t) * (s - t) ≥ 0)
    {u : Ω → ℝ} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f ω (u ω) - f ω (v ω)) * (u ω - v ω)) μ ∧
    0 ≤ ∫ ω : Ω, (f ω (u ω) - f ω (v ω)) * (u ω - v ω) ∂μ := by
  simp only [←inner_eq_mul]
  refine hf.nonneg_integral_nemytskii_sub_nemytskii_inner_memLp_sub_memLp_of_monotone_of_growth hpq haq hC hfaCpq ?_ hup hvp
  simpa only [inner_eq_mul] using hf0
