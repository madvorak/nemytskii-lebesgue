import NemytskiiLebesgue.Continuity
import NemytskiiLebesgue.RealIso

open MeasureTheory Filter
open scoped ENNReal Topology

section irrelevant

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma const_zero_memLp_one : MemLp ↓(0 : ℝ) 1 μ := by
  simp

private lemma normSMulSelf_growth :
    ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^1, ‖normSMulSelf ω ξ‖ ≤ |0| + 1 * ‖ξ‖ ^ ((2 : ℝ≥0∞) / 1).toReal := by
  filter_upwards with ω ξ
  norm_num [normSMulSelf, norm_smul, pow_two]

private theorem usage_seq_continuous
    (uₙ : ℕ → Ω → ℝ^1) (huₙ : ∀ n : ℕ, MemLp (uₙ n) 2 μ)
    (u : Ω → ℝ^1) (hu2 : MemLp u 2 μ)
    (huuₙ : Tendsto (fun n : ℕ => eLpNorm (uₙ n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω : Ω => normSMulSelf ω (uₙ n ω) - normSMulSelf ω (u ω)) 1 μ)
      atTop (𝓝 0) :=
  normSMulSelf_isCaratheodory.nemytskii_seqContinuous_of_memLp_of_growth_real
    one_le_two
    ENNReal.ofNat_lt_top
    le_rfl
    ENNReal.one_lt_top
    const_zero_memLp_one
    zero_le_one
    normSMulSelf_growth
    huₙ
    hu2
    huuₙ

end irrelevant

example {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {uₙ : ℕ → Ω → ℝ} (huₙ : ∀ n : ℕ, MemLp (uₙ n) 2 μ)
    {u : Ω → ℝ} (hu : MemLp u 2 μ)
    (huuₙ : Tendsto (fun n : ℕ => eLpNorm (uₙ n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm (fun ω : Ω => |uₙ n ω| * (uₙ n ω) - |u ω| * (u ω)) 1 μ) atTop (𝓝 0) := by
  have hL : ∀ v : Ω → ℝ, MemLp v 2 μ → MemLp (fun ω : Ω => realLIE (v ω)) 2 μ := ↓(by
    simpa using ·.continuousLinearMap_comp realLIE.toContinuousLinearEquiv.toContinuousLinearMap)
  have key := usage_seq_continuous (realLIE <| uₙ · ·) (hL _ <| huₙ ·) (realLIE <| u ·) (hL _ hu) ?_
  · refine key.congr ↓?_
    apply eLpNorm_congr_norm_ae
    filter_upwards with
    rw [normSMulSelf_realLIE, normSMulSelf_realLIE, ←map_sub, norm_realLIE]
    repeat rw [Real.norm_eq_abs]
  · refine huuₙ.congr (fun n : ℕ => ?_)
    apply eLpNorm_congr_norm_ae
    filter_upwards with ω
    show |(uₙ n - u) ω| = ‖realLIE (uₙ n ω) - realLIE (u ω)‖
    rewrite [←map_sub, norm_realLIE]
    rfl
