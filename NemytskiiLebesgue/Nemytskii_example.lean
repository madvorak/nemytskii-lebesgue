import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.Nemytskii

open MeasureTheory
open scoped ENNReal

example {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : Ω → ℝ} (hu3 : MemLp u 3 μ)
    {v : Ω → ℝ} (hv3 : MemLp v 3 μ) :
    Integrable (fun ω : Ω => (u ω * |u ω| - v ω * |v ω|) * (u ω - v ω)) μ ∧
                0 ≤ ∫ ω : Ω, (u ω * |u ω| - v ω * |v ω|) * (u ω - v ω) ∂μ := by
  have hpq : Real.HolderConjugate (3 : ℝ) (3 / 2 : ℝ) := by constructor <;> norm_num
  have haCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ,
      |(fun (_ : Ω) (ξ : ℝ) => ξ * |ξ|) ω ξ| ≤
      |(0 : Ω → ℝ) ω| + 1 * |ξ| ^ ((3 : ℝ) / (3 / 2)) := by
    refine ae_of_all _ ↓↓?_
    have h32 : ((3 : ℝ) / (3 / 2)) = 2 := by norm_num
    rw [h32, abs_mul, abs_abs, Real.rpow_two]
    simp [pow_two]
  have h0 : ∀ᵐ ω ∂μ, ∀ s t : ℝ,
      (↓(fun ξ : ℝ => ξ * |ξ|) ω s -
       ↓(fun ξ : ℝ => ξ * |ξ|) ω t
      ) * (s - t) ≥
      0 := by
    refine ae_of_all _ (fun ω s t => ?_)
    rcases le_total 0 s with hs | hs <;>
    rcases le_total 0 t with ht | ht <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hs, ht] <;>
    nlinarith [abs_nonneg s, abs_nonneg t, sq_nonneg (s - t), sq_nonneg (s + t)]
  have hup : MemLp u ↱3 μ := by
    convert hu3
    norm_num
  have hvp : MemLp v ↱3 μ := by
    convert hv3
    norm_num
  exact
    (Function.IsCaratheodory.of_continuous (continuous_id.mul continuous_abs)
    ).nonneg_integral_nemytskii_sub_nemytskii_mul_memLp_sub_memLp_of_monotone_of_growth_real hpq MemLp.zero zero_le_one haCpq h0 hup hvp
