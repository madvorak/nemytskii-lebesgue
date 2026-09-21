import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.Frechet
import NemytskiiLebesgue.RealIso

open MeasureTheory
open scoped InnerProductSpace ENNReal

private noncomputable def μ1 : Measure ℝ := volume.restrict (Set.Ioo (-1) 1)

section irrelevant

private instance : IsFiniteMeasure μ1 := by
  unfold μ1
  infer_instance

private noncomputable def normSMulSelfFD : ℝ → ℝ^1 → (ℝ^1 →L[ℝ] ℝ^1) :=
  ↓(fun ξ : ℝ^1 => (2 * ‖ξ‖) • ContinuousLinearMap.id ℝ ℝ^1)

private lemma normSMulSelfFD_isCaratheodory : normSMulSelfFD.IsCaratheodory μ1 :=
  Function.IsCaratheodory.of_continuous
    ((continuous_const.mul continuous_norm).smul continuous_const)

private lemma normSMulSelf_hasFDerivAt (ω : ℝ) (ξ : ℝ^1) : HasFDerivAt (normSMulSelf ω) (normSMulSelfFD ω ξ) ξ := by
  unfold normSMulSelf normSMulSelfFD
  rcases eq_or_ne ξ 0 with rfl | h
  · have hz : (2 * ‖(0 : ℝ^1)‖) • ContinuousLinearMap.id ℝ ℝ^1 = 0 := by
      rw [norm_zero, mul_zero]
      exact zero_smul ℝ (ContinuousLinearMap.id ℝ ℝ^1)
    rw [hz, hasFDerivAt_iff_tendsto]
    simp only [sub_zero, zero_apply, norm_zero, zero_smul]
    have hcong : (fun x : ℝ^1 => ‖x‖⁻¹ * ‖‖x‖ • x‖) =ᶠ[nhds 0] (‖·‖) := by
      filter_upwards [] with x
      by_cases hx : x = 0
      · simp [hx]
      · rw [norm_smul, norm_norm]
        field_simp
    apply Filter.Tendsto.congr' hcong.symm
    simpa using (continuous_norm (E := ℝ^1)).tendsto 0
  · have hpos : 0 < ‖ξ‖ := by positivity
    have hsqeq : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 := by
      simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs, sq_abs]
    have hnorm : HasFDerivAt (‖·‖) (‖ξ‖⁻¹ • innerSL ℝ ξ) ξ := by
      have hsq : HasFDerivAt (‖·‖ ^ 2) ((2 : ℕ) • innerSL ℝ ξ) ξ :=
        (hasFDerivAt_id ξ).norm_sq
      have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖ξ‖ ^ 2))) (‖ξ‖ ^ 2) :=
        Real.hasDerivAt_sqrt (pow_ne_zero 2 hpos.ne')
      have hcomp := hsqrt.comp_hasFDerivAt ξ hsq
      have heq : (Real.sqrt ∘ fun x : ℝ^1 => ‖x‖ ^ 2) = (‖·‖) := by
        funext
        simp
      rw [heq] at hcomp
      convert! hcomp using 1
      rw [Real.sqrt_sq_eq_abs, abs_norm]
      ext
      simp only [smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
      rw [mul_comm (2 : ℝ), ←mul_assoc]
      field_simp
    convert! hnorm.smul (hasFDerivAt_id ξ) using 1
    ext v i
    fin_cases i
    have hinner : ⟪ξ, v⟫_ℝ = ξ 0 * v 0 := by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul, innerSL_apply_apply, id_eq, PiLp.add_apply, PiLp.smul_apply,
      Fin.zero_eta, Fin.isValue]
    rw [hinner]
    field_simp
    linear_combination v 0 * hsqeq

private lemma exHolderTriple : Real.HolderTriple (1 : ℝ) 2 (2 / 3) := by
  constructor <;> norm_num

private lemma exGrowth (ω : ℝ) (ξ : ℝ^1) :
    ‖normSMulSelfFD ω ξ‖ ≤ (1 : ℝ) + 1 * ‖ξ‖ ^ ((2 : ℝ) / 1) := by
  rw [normSMulSelfFD, norm_smul, ContinuousLinearMap.norm_id, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_one, Real.rpow_two]
  linarith [sq_nonneg (‖ξ‖ - 1), norm_nonneg ξ]

private theorem exNemytskiiMap_frechet_deriv
    (u : ℝ → ℝ^1) (hu : MemLp u ↱2 μ1) :
    ∀ ε > 0, ∃ δ > 0, ∀ l : ℝ → ℝ^1,
      MemLp l ↱2 μ1 →
        eLpNorm l ↱2 μ1 ≤ ↱δ →
          eLpNorm (fun ω : ℝ => normSMulSelf ω (u ω + l ω) - normSMulSelf ω (u ω) - normSMulSelfFD ω (u ω) (l ω)) ↱(2 / 3 : ℝ) μ1 ≤
          ↱ε * eLpNorm l ↱2 μ1 :=
  normSMulSelf_isCaratheodory.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
    normSMulSelfFD_isCaratheodory
    (ae_of_all _ normSMulSelf_hasFDerivAt)
    one_le_two
    (le_refl 1)
    exHolderTriple
    (ae_of_all _ ↓zero_le_one)
    (memLp_const _)
    one_pos
    (ae_of_all _ exGrowth)
    hu

end irrelevant

example (u : ℝ → ℝ) (hu : MemLp u 2 μ1) :
    ∀ ε > 0, ∃ δ > 0, ∀ l : ℝ → ℝ,
      MemLp l 2 μ1 →
        eLpNorm l 2 μ1 ≤ ↱δ →
          eLpNorm (fun ω : ℝ => |u ω + l ω| * (u ω + l ω) - |u ω| * (u ω) - 2 * |u ω| * (l ω)) (2 / 3) μ1 ≤
          ↱ε * eLpNorm l 2 μ1 := by
  intro ε hε
  have hu2 : MemLp (realLIE <| u ·) ↱2 μ1 := by
    simpa using memLp_realLIE hu
  obtain ⟨δ, hδ, H⟩ := exNemytskiiMap_frechet_deriv (realLIE <| u ·) hu2 ε hε
  refine ⟨δ, hδ, fun l hl hlδ => ?_⟩
  have hl2 : MemLp (realLIE <| l ·) ↱2 μ1 := by
    simpa using memLp_realLIE hl
  simp only [←Real.norm_eq_abs]
  have Hspec := H (realLIE <| l ·) hl2 (by rw [eLpNorm_realLIE]; convert hlδ; norm_num)
  rw [eLpNorm_realLIE] at Hspec
  rw [show eLpNorm l 2 μ1 = eLpNorm l ↱2 μ1 by norm_num]
  have hnormSMulSelfFD : ∀ ω : ℝ, ∀ a b : ℝ, normSMulSelfFD ω (realLIE a) (realLIE b) = realLIE (2 * |a| * b) := by
    intros
    simp only [normSMulSelfFD, smul_apply, ContinuousLinearMap.id_apply, norm_realLIE]
    rw [realLIE_mul]
  refine le_of_eq_of_le (eLpNorm_congr_norm_ae ?_) (natCast_div_natCast_eq_ofReal 2 (Nat.zero_ne_add_one 2).symm ▸ Hspec)
  filter_upwards with
  rw [←map_add, normSMulSelf_realLIE, normSMulSelf_realLIE, hnormSMulSelfFD, ←map_sub, ←map_sub, norm_realLIE]
  repeat rw [Real.norm_eq_abs]
