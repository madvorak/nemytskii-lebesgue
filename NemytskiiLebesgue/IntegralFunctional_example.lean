import NemytskiiLebesgue.IntegralFunctional

open MeasureTheory
open scoped ENNReal

open scoped RealInnerProductSpace

private noncomputable def μ1 : Measure ℝ := volume.restrict (Set.Ioo (-1) 1)

private instance : IsFiniteMeasure μ1 := by
  unfold μ1
  infer_instance

private noncomputable def cubicNorm : ℝ → ℝ → ℝ := ↓(fun ξ : ℝ => ((1 : ℝ) / 3) * |ξ| ^ (3 : ℝ))

private noncomputable def cubicNormDeriv : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := ↓(fun ξ : ℝ => |ξ| • innerSL ℝ ξ)

private lemma cubicNorm_caratheodory : cubicNorm.IsCaratheodory μ1 := by
  apply Function.IsCaratheodory.of_continuous
  apply continuous_const.mul
  apply continuous_norm.rpow_const
  intro
  right
  norm_num

private lemma cubicNormDeriv_caratheodory : cubicNormDeriv.IsCaratheodory μ1 := by
  apply Function.IsCaratheodory.of_continuous
  fun_prop

private lemma cubicNorm_hasFDerivAt (ω : ℝ) (ξ : ℝ) : HasFDerivAt (cubicNorm ω) (cubicNormDeriv ω ξ) ξ := by
  unfold cubicNorm cubicNormDeriv
  convert! (hasFDerivAt_norm_rpow ξ (show 1 < 3 by norm_num)).const_mul (1 / 3 : ℝ) using 1
  rw [smul_smul]
  norm_num
  congr 1
  ring

private lemma cubicNorm_growth (ω : ℝ) (ξ : ℝ) :
    |cubicNorm ω ξ| ≤ |(0 : ℝ)| + (1 / 3) * |ξ| ^ ((3 : ℝ≥0∞).toReal) := by
  unfold cubicNorm
  simp

private lemma cubicNormDeriv_growth (ω : ℝ) (ξ : ℝ) :
    ‖cubicNormDeriv ω ξ‖ ≤ (0 : ℝ) + 1 * |ξ| ^ ((3 : ℝ) - 1) := by
  unfold cubicNormDeriv
  rw [norm_smul, innerSL_apply_norm]
  have h2 : |ξ| ^ ((3 : ℝ) - 1) = |ξ| * |ξ| := by
    rw [show ((3 : ℝ) - 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [h2]
  repeat rw [Real.norm_eq_abs]
  simp

private theorem example_wellDefined (u : ℝ → ℝ) (hup : MemLp u 3 μ1) :
    Integrable (fun ω : ℝ => cubicNorm ω (u ω)) μ1 :=
  cubicNorm_caratheodory.integralFunctional_wellDefined
    (by norm_num)
    (by norm_num)
    (integrable_zero ℝ ℝ μ1)
    (by norm_num)
    (Filter.Eventually.of_forall cubicNorm_growth)
    hup

private noncomputable def cubicNorm1 : ℝ → ℝ^1 → ℝ := ↓(fun ξ : ℝ^1 => ((1 : ℝ) / 3) * ‖ξ‖ ^ (3 : ℝ))

private noncomputable def cubicNormDeriv1 : ℝ → ℝ^1 → (ℝ^1 →L[ℝ] ℝ) := ↓(fun ξ : ℝ^1 => ‖ξ‖ • innerSL ℝ ξ)

private lemma cubicNorm1_caratheodory : cubicNorm1.IsCaratheodory μ1 := by
  apply Function.IsCaratheodory.of_continuous
  exact continuous_const.mul (continuous_norm.rpow_const ↓(Or.inr zero_le_three))

private lemma cubicNormDeriv1_caratheodory : cubicNormDeriv1.IsCaratheodory μ1 := by
  apply Function.IsCaratheodory.of_continuous
  fun_prop

private lemma cubicNorm1_hasFDerivAt (ω : ℝ) (ξ : ℝ^1) : HasFDerivAt (cubicNorm1 ω) (cubicNormDeriv1 ω ξ) ξ := by
  unfold cubicNorm1 cubicNormDeriv1
  convert! (hasFDerivAt_norm_rpow ξ (show 1 < 3 by norm_num)).const_mul (1 / 3 : ℝ) using 1
  rw [smul_smul]
  norm_num
  ring_nf

private lemma cubicNormDeriv1_growth (ω : ℝ) (ξ : ℝ^1) :
    ‖cubicNormDeriv1 ω ξ‖ ≤ (0 : ℝ) + 1 * ‖ξ‖ ^ ((3 : ℝ) - 1) := by
  unfold cubicNormDeriv1
  rw [norm_smul, innerSL_apply_norm, norm_norm]
  have hξ : ‖ξ‖ ^ ((3 : ℝ) - 1) = ‖ξ‖ * ‖ξ‖ := by
    rw [show ((3 : ℝ) - 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hξ]
  linarith

private lemma cubicNorm1_realLIE (ω : ℝ) (x : ℝ) : cubicNorm1 ω (realLIE x) = cubicNorm ω x := by
  simp only [cubicNorm1, cubicNorm, norm_realLIE]

private lemma cubicNormDeriv1_realLIE (ω : ℝ) (x y : ℝ) : cubicNormDeriv1 ω (realLIE x) (realLIE y) = cubicNormDeriv ω x y := by
  simp only [cubicNormDeriv1, cubicNormDeriv, smul_apply, innerSL_apply_apply, realLIE.inner_map_map, norm_realLIE]

private noncomputable def innerPow {n : ℕ} (A : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)) (α : ℝ^n → ℝ) : ℝ^n → ℝ^n → ℝ :=
  fun x ξ => |⟪A x ξ, ξ⟫| ^ α x

private lemma abs_inner_le_opNorm_sq {n : ℕ} (A : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)) (x ξ : ℝ^n) :
    |⟪A x ξ, ξ⟫| ≤ ‖A x‖ * ‖ξ‖ ^ 2 :=
  le_trans (abs_real_inner_le_norm _ _) (by nlinarith [norm_nonneg (A x ξ), norm_nonneg ξ, (A x).le_opNorm ξ])

private lemma rpow_le_one_add_rpow {t e p : ℝ} (ht : 0 ≤ t) (he : 0 ≤ e) (hep : e ≤ p) :
    t ^ e ≤ 1 + t ^ p := by
  by_cases ht1 : t ≤ 1
  · exact le_add_of_le_of_nonneg (Real.rpow_le_one ht ht1 he) (Real.rpow_nonneg ht _)
  · exact le_add_of_nonneg_of_le zero_le_one (Real.rpow_le_rpow_of_exponent_le (Std.le_of_not_ge ht1) hep)

private lemma innerPow_isCaratheodory {n : ℕ} {μ : Measure ℝ^n}
    {A : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)} (hA : Measurable A)
    {α : ℝ^n → ℝ} (hα : Measurable α) (α_nonneg : ∀ᵐ x : ℝ^n ∂μ, 0 ≤ α x) :
    (innerPow A α).IsCaratheodory μ := by
  constructor
  · intro x
    apply Measurable.stronglyMeasurable
    apply Measurable.pow
    · fun_prop
    · exact hα
  · filter_upwards [α_nonneg] with x hx
    apply Continuous.rpow_const
    · fun_prop
    · simp [*]

private lemma innerPow_growth {n : ℕ} {μ : Measure ℝ^n}
    {M : ℝ} (hM : 0 ≤ M)
    {A : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)} (hAM : ∀ᵐ x : ℝ^n ∂μ, ‖A x‖ ≤ M)
    {α : ℝ^n → ℝ} (hα : ∀ᵐ x : ℝ^n ∂μ, 0 ≤ α x)
    {α' : ℝ} (hαα' : ∀ᵐ x : ℝ^n ∂μ, α x ≤ α')
    {p : ℝ≥0∞} (hαp : 2 * α' ≤ p.toReal) :
    ∀ᵐ x : ℝ^n ∂μ, ∀ ξ : ℝ^n,
      ‖innerPow A α x ξ‖ ≤ |(1 + M) ^ α'| + (1 + M) ^ α' * ‖ξ‖ ^ p.toReal := by
  have hinnerPow_growth : ∀ᵐ x : ℝ^n ∂μ, ∀ ξ : ℝ^n, |⟪A x ξ, ξ⟫| ^ (α x) ≤ (1 + M) ^ (α') * (1 + ‖ξ‖ ^ p.toReal) := by
    filter_upwards [hAM, hα, hαα'] with x hxA hxpos hxhi
    intro ξ
    refine' le_trans (Real.rpow_le_rpow (abs_nonneg _) (show |⟪(A x) ξ, ξ⟫| ≤ (1 + M) * ‖ξ‖ ^ 2 from _) (by positivity)) _
    · exact le_trans (abs_inner_le_opNorm_sq A x ξ) (by nlinarith [norm_nonneg ξ])
    · rw [Real.mul_rpow (by positivity) (by positivity), ←Real.rpow_natCast, ←Real.rpow_mul (norm_nonneg ξ)]
      norm_num
      gcongr
      · linarith
      · by_cases hξ : ‖ξ‖ ≤ 1
        · exact le_add_of_le_of_nonneg (Real.rpow_le_one (norm_nonneg _) hξ (by positivity)) (by positivity)
        · exact le_add_of_nonneg_of_le zero_le_one (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  filter_upwards [hinnerPow_growth] with x hx ξ
  simp only [innerPow]
  have hnn : (0 : ℝ) ≤ |⟪A x ξ, ξ⟫| ^ α x := Real.rpow_nonneg (abs_nonneg _) _
  have hK : (0 : ℝ) ≤ (1 + M) ^ α' := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg hnn, abs_of_nonneg hK]
  have hx' := hx ξ
  rw [mul_add, mul_one] at hx'
  linarith

example
    {n : ℕ} (s : Set ℝ^n) (hs : volume s < ⊤)
    {A : ℝ^n → (ℝ^n →L[ℝ] ℝ^n)} (hA : Measurable A)
    {α : ℝ^n → ℝ} (hα : Measurable α)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {M : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x : ℝ^n ∂(volume.restrict s), ‖A x‖ ≤ M)
    {β : ℝ} (hβ : 0 < β)
    (hβα : ∀ᵐ x : ℝ^n ∂(volume.restrict s), β ≤ α x)
    {α' : ℝ} (hαα' : ∀ᵐ x : ℝ^n ∂(volume.restrict s), α x ≤ α')
    (hαp : α' ≤ p.toReal / 2)
    {u : ℝ^n → ℝ^n} (hup : MemLp u p (volume.restrict s)) :
    Integrable (fun x : ℝ^n => innerPow A α x (u x)) (volume.restrict s) := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.← hs.ne
  have α_nonneg : ∀ᵐ x : ℝ^n ∂(volume.restrict s), 0 ≤ α x := by
    filter_upwards [hβα] with x hx using le_trans hβ.le hx
  have hαp' : 2 * α' ≤ p.toReal := by linarith
  exact
    (innerPow_isCaratheodory hA hα α_nonneg).integralFunctional_wellDefined_real
      h1p
      hp
      (integrable_const _)
      (Real.rpow_nonneg (by linarith) _)
      (innerPow_growth hM hAM α_nonneg hαα' hαp')
      hup

example (u : ℝ → ℝ) (hup : MemLp u 3 μ1) :
    (∀ v : ℝ → ℝ, MemLp v 3 μ1 →
      Integrable (fun ω : ℝ => (cubicNormDeriv ω (u ω)) (v ω)) μ1) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ l : ℝ → ℝ, MemLp l 3 μ1 →
      eLpNorm l 3 μ1 ≤ ↱δ →
        |∫ ω : ℝ, (cubicNorm ω (u ω + l ω) - cubicNorm ω (u ω) - (cubicNormDeriv ω (u ω)) (l ω)) ∂μ1| ≤
        ε * (eLpNorm l 3 μ1).toReal) := by
  have h3 : (↱(3 : ℝ) : ℝ≥0∞) = 3 := by norm_num
  have hup3 : MemLp u ↱(3 : ℝ) μ1 := h3 ▸ hup
  obtain ⟨part1, part2⟩ :=
    cubicNorm1_caratheodory.integralFunctional_frechet_deriv
      cubicNormDeriv1_caratheodory
      (Filter.Eventually.of_forall cubicNorm1_hasFDerivAt)
      (show Real.HolderConjugate 3 (3 / 2) by constructor <;> norm_num)
      (Filter.Eventually.of_forall ↓(le_refl 0))
      (memLp_const 0)
      zero_lt_one
      (Filter.Eventually.of_forall cubicNormDeriv1_growth)
      (memLp_realLIE hup3)
  constructor
  · intro v hv
    have hv3 : MemLp v ↱(3 : ℝ) μ1 := h3 ▸ hv
    exact (part1 (realLIE <| v ·) (memLp_realLIE hv3)).congr
        (Filter.Eventually.of_forall (fun ω : ℝ => (cubicNormDeriv1_realLIE ω (u ω) (v ω))))
  · intro ε hε
    obtain ⟨δ, hδ, hb⟩ := part2 ε hε
    refine ⟨δ, hδ, fun l hl hl' => ?_⟩
    have hl3 : MemLp l ↱(3 : ℝ) μ1 := h3 ▸ hl
    have key := hb (realLIE <| l ·) (memLp_realLIE hl3) (eLpNorm_realLIE l ▸ h3 ▸ hl')
    rw [eLpNorm_realLIE, h3] at key
    refine le_trans (le_of_eq ?_) key
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall ↓?_)
    simp only [←realLIE.map_add, cubicNorm1_realLIE, cubicNormDeriv1_realLIE]
