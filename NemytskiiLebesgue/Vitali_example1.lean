import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.Vitali
import NemytskiiLebesgue.RealIso

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

private noncomputable def μ1 : Measure ℝ := volume.restrict (Set.Ioo (-1) 1)

section irrelevant

private instance : IsFiniteMeasure μ1 := by
  unfold μ1
  infer_instance

private noncomputable def absMulSelfAddOne (Ω : Type) : Ω → ℝ^1 → ℝ^1 :=
  ↓(fun ξ : ℝ^1 => ‖ξ‖ • ξ + realLIE 1)

private lemma absMulSelfAddOne_growth {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) :
    ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^1,
      ‖absMulSelfAddOne Ω ω ξ‖ ≤ |(↓1 : Ω → ℝ) ω| + (1 : ℝ) * ‖ξ‖ ^ (((4 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal) := by
  filter_upwards with ω ξ
  have h4 : (((4 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal) = 2 := by norm_num
  rw [h4]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_norm, norm_realLIE, Real.rpow_two, pow_two]
  have h1 : |(↓1 : Ω → ℝ) ω| = 1 := by simp
  linarith only [h1]

private lemma absMulSelfAddOne_comp_realLIE {Ω : Type} (u : Ω → ℝ) :
    (fun ω : Ω => absMulSelfAddOne Ω ω (realLIE (u ω))) =
    (fun ω : Ω => realLIE (‖u ω‖ * u ω + 1)) := by
  funext
  rewrite [absMulSelfAddOne, norm_realLIE, ←smul_eq_mul]
  rfl

private noncomputable def coerciveF : ℝ → ℝ^1 → ℝ^1 :=
  fun ω ξ => realLIE ω + ‖ξ‖ • ξ

private noncomputable def coerciveB : ℝ → ℝ :=
  ((2 / 3 : ℝ) * |·| ^ (3 / 2 : ℝ))

private lemma memLp_of_realLIE {p : ℝ≥0∞} {g : ℝ → ℝ}
    (hgp : MemLp (fun ω : ℝ => realLIE (g ω)) p μ1) :
    MemLp g p μ1 := by
  constructor
  · exact realLIE.symm.continuous.comp_aestronglyMeasurable hgp.left
  · rw [←eLpNorm_realLIE g]
    exact hgp.right

private lemma coerciveF_comp (ω x : ℝ) :
    coerciveF ω (realLIE x) = realLIE (ω + |x| * x) := by
  simp [coerciveF, ←smul_eq_mul, map_smul]

private lemma coerciveF_caratheodory : coerciveF.IsCaratheodory μ1 :=
  (Function.IsCaratheodory.of_stronglyMeasurable realLIE.continuous.stronglyMeasurable).add
    normSMulSelf_isCaratheodory

private lemma coercive_a_memLp : MemLp (fun ω : ℝ => ω) ↱(3 / 2) μ1 := by
  apply MemLp.of_bound (C := 1) (by fun_prop)
  rw [μ1, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with ω hω
  simp only [Real.norm_eq_abs]
  rw [abs_le]
  exact ⟨hω.left.le, hω.right.le⟩

private lemma coerciveB_integrable : Integrable coerciveB μ1 := by
  have conti : Continuous coerciveB :=
    continuous_const.mul (continuous_abs.rpow_const ↓(Or.inr (by norm_num)))
  have hμ1 : MemLp coerciveB 1 μ1 := by
    apply MemLp.of_bound (C := 2 / 3) conti.aestronglyMeasurable
    rw [μ1, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with ω hω
    have hω1 : |ω| ≤ 1 := by
      rw [abs_le]
      exact ⟨hω.left.le, hω.right.le⟩
    have : |ω| ^ (3 / 2 : ℝ) ≤ 1 := by
      calc |ω| ^ (3 / 2 : ℝ) ≤ 1 ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (abs_nonneg _) hω1 (by norm_num)
        _ = 1 := Real.one_rpow (3 / 2)
    unfold coerciveB
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [Real.rpow_nonneg (abs_nonneg ω) (3 / 2 : ℝ)]
  exact hμ1.integrable le_rfl

private lemma coerciveF_growth :
    ∀ᵐ ω ∂μ1, ∀ ξ : ℝ^1,
      ‖coerciveF ω ξ‖ ≤ |(fun ω : ℝ => ω) ω| + (1 : ℝ) * ‖ξ‖ ^ ((3 : ℝ) / (3 / 2)) := by
  refine Filter.Eventually.of_forall ↓↓?_
  have h32 : ((3 : ℝ) / (3 / 2)) = 2 := by norm_num
  rw [h32]
  apply le_trans (norm_add_le _ _)
  rw [norm_smul, norm_norm]
  simp only [norm_realLIE]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from Nat.cast_two.symm, Real.rpow_natCast]
  linarith

private lemma coercive_scalar_key (ω s : ℝ) :
    ω * s + (1 / 3 : ℝ) * |s| ^ (3 : ℝ) + (2 / 3 : ℝ) * |ω| ^ (3 / 2 : ℝ) ≥ 0 := by
  set r := Real.sqrt |ω| with r_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg |ω|
  have hr2 : r ^ 2 = |ω| := Real.sq_sqrt (abs_nonneg ω)
  have hs3 : |s| ^ (3 : ℝ) = |s| ^ 3 := by
    rw [←Real.rpow_natCast |s| 3]
    norm_num
  have h32r : |ω| ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [r_def, Real.sqrt_eq_rpow, ←Real.rpow_natCast (|ω| ^ ((1 : ℝ) / 2)) 3,
        ←Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [hs3, h32r]
  have h0s : 0 ≤ |s| := abs_nonneg _
  have hsrrs : |s| ^ 3 + 2 * r ^ 3 ≥ 3 * r ^ 2 * |s| := by
    nlinarith [sq_nonneg (|s| - r),
      mul_nonneg (sq_nonneg (|s| - r)) (add_nonneg h0s (mul_nonneg zero_le_two hr0))]
  have hωs : ω * s ≥ - (r ^ 2 * |s|) := by
    nlinarith [neg_abs_le (ω * s), abs_mul ω s, hr2]
  nlinarith [hsrrs, hωs]

private lemma coerciveF_coercive :
    ∀ᵐ ω ∂μ1, ∀ ξ : ℝ^1,
      ⟪coerciveF ω ξ, ξ⟫ ≥ (2 / 3 : ℝ) * ‖ξ‖ ^ (3 : ℝ) - coerciveB ω := by
  filter_upwards with ω ξ
  unfold coerciveF coerciveB
  set s := realLIE.symm ξ with s_def
  have hξ : ξ = realLIE s := by simp [s_def]
  rw [hξ, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, realLIE.inner_map_map, norm_realLIE]
  have hωs : (⟪ω, s⟫ : ℝ) = ω * s := by simp [mul_comm]
  rw [hωs]
  have hsss : |s| * |s| ^ (2 : ℕ) = |s| ^ (3 : ℝ) := by
    rw [Nat.cast_three.symm, Real.rpow_natCast]
    ring
  rw [hsss]
  linarith [coercive_scalar_key ω s]

private lemma integral_norm_cube_eq {u : ℝ → ℝ} (hu : MemLp u 3 μ1) :
    ∫ ω : ℝ, |u ω| ^ (3 : ℝ) ∂μ1 = ((eLpNorm u 3 μ1) ^ (3 : ℝ)).toReal := by
  have hI : 0 ≤ ∫ ω : ℝ, |u ω| ^ (3 : ℝ) ∂μ1 :=
    integral_nonneg (fun ω : ℝ => Real.rpow_nonneg (abs_nonneg _) _)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (Ne.symm (NeZero.ne' 3)) (Ne.symm ENNReal.top_ne_ofNat) hu]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_three,
      ENNReal.toReal_ofReal (by positivity)]
  refine Eq.symm (Real.rpow_inv_rpow hI ?_)
  norm_num

private lemma integral_coerciveB_eq :
    ∫ ω : ℝ, |coerciveB ω| ∂μ1 = (eLpNorm coerciveB 1 μ1).toReal := by
  have hB : MemLp coerciveB 1 μ1 := memLp_one_iff_integrable.← coerciveB_integrable
  have hI : 0 ≤ ∫ ω : ℝ, |coerciveB ω| ∂μ1 := integral_nonneg ↓(abs_nonneg _)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top hB]
  simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]
  exact Eq.symm (ENNReal.toReal_ofReal hI)

private lemma example332 : Real.HolderConjugate 3 (3 / 2) := by
  rw [Real.holderConjugate_iff]
  norm_num

private lemma norm_normSMulSelf_le :
    ∀ᵐ ω ∂μ1, ∀ ξ : ℝ^1,
      ‖normSMulSelf ω ξ‖ ≤ |0| + (1 : ℝ) * ‖ξ‖ ^ ((3 : ℝ) / (3 / 2)) := by
  refine Filter.Eventually.of_forall ↓↓?_
  have h3322 : ((3 : ℝ) / (3 / 2)) = 2 := by norm_num
  simp [h3322, normSMulSelf, norm_smul, pow_two]

private lemma normSmul_strong_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) :
    (1 / 2 : ℝ) * ‖a - b‖ ^ (3 : ℝ) ≤ ⟪‖a‖ • a - ‖b‖ • b, a - b⟫ := by
  have hab3 : ‖a - b‖ ^ (3 : ℝ) = ‖a - b‖ ^ (3 : ℕ) := by
    rw [←Real.rpow_natCast ‖a - b‖ 3]
    norm_num
  have haabb :
      (⟪‖a‖ • a - ‖b‖ • b, a - b⟫ : ℝ) =
      ‖a‖ ^ 3 + ‖b‖ ^ 3 - (‖a‖ + ‖b‖) * ⟪a, b⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm b a]
    ring
  rw [hab3, haabb]
  have hab : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have hab2 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_sub_sq_real a b
  have h0aa : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have h0bb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have h0ab : (0 : ℝ) ≤ ‖a - b‖ := norm_nonneg (a - b)
  nlinarith [mul_nonneg (add_nonneg h0aa h0bb) (sq_nonneg (‖a‖ - ‖b‖)),
             mul_nonneg (sq_nonneg ‖a - b‖) (sub_nonneg.← hab),
             mul_nonneg h0ab (sub_nonneg.← hab)]

private lemma example_hfCp :
    ∀ᵐ ω ∂μ1, ∀ ξ η : ℝ^1,
      ⟪normSMulSelf ω ξ - normSMulSelf ω η, ξ - η⟫ ≥ (1 / 2 : ℝ) * ‖ξ - η‖ ^ (3 : ℝ) :=
  Filter.Eventually.of_forall ↓normSmul_strong_mono

private noncomputable def absMulSelf : ℝ → ℝ → ℝ := ↓(fun x : ℝ => |x| * x)

private lemma absMulSelf_caratheodory : absMulSelf.IsCaratheodory μ1 :=
  Function.IsCaratheodory.of_continuous (by fun_prop)

private lemma norm_absMulSelf_le :
    ∀ᵐ ω ∂μ1, ∀ ξ : ℝ,
      |absMulSelf ω ξ| ≤ |(0 : ℝ → ℝ) ω| + (1 : ℝ) * |ξ| ^ ((3 : ℝ) / (3 / 2)) := by
  filter_upwards with ω ξ
  have h3322 : ((3 : ℝ) / (3 / 2)) = 2 := by norm_num
  simp [h3322, absMulSelf, pow_two]

private lemma absMulSelf_hfCp :
    ∀ᵐ ω ∂μ1, ∀ ξ η : ℝ,
      ⟪absMulSelf ω ξ - absMulSelf ω η, ξ - η⟫ ≥ (1 / 2 : ℝ) * |ξ - η| ^ (3 : ℝ) := by
  apply Filter.Eventually.of_forall
  intro
  simp only [absMulSelf, ←smul_eq_mul]
  exact normSmul_strong_mono

private lemma ofReal3div2 : 3 / 2 = ↱(3 / 2) :=
  natCast_div_natCast_eq_ofReal 3 two_ne_zero

end irrelevant

example
    {u : ℝ → ℝ^1} (hu : MemLp u ↱3 μ1) :
    MemLp (fun ω : ℝ => normSMulSelf ω (u ω)) ↱(3 / 2) μ1 :=
  normSMulSelf_isCaratheodory.memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
    example332
    MemLp.zero
    zero_le_one
    norm_normSMulSelf_le
    hu

example
    {u : ℝ → ℝ^1} (hu : MemLp u ↱3 μ1)
    {v : ℝ → ℝ^1} (hv : MemLp v ↱3 μ1) :
    Integrable (fun ω : ℝ => ⟪normSMulSelf ω (u ω) - normSMulSelf ω (v ω), u ω - v ω⟫) μ1 :=
  normSMulSelf_isCaratheodory.integrable_nemyckii_sub_nemytskii_inner_memLp_sub_memLp_of_growth_of_holderConjugate_real
    example332
    MemLp.zero
    zero_le_one
    norm_normSMulSelf_le
    hu
    hv

example
    {u : ℝ → ℝ^1} (hu : MemLp u ↱3 μ1)
    {v : ℝ → ℝ^1} (hv : MemLp v ↱3 μ1) :
    Integrable
      (fun ω : ℝ => ⟪normSMulSelf ω (u ω) - normSMulSelf ω (v ω), u ω - v ω⟫) μ1 ∧
    ∫ ω : ℝ, ⟪normSMulSelf ω (u ω) - normSMulSelf ω (v ω), u ω - v ω⟫ ∂μ1 ≥
      (1 / 2 : ℝ) * ∫ ω : ℝ, ‖u ω - v ω‖ ^ (3 : ℝ) ∂μ1 :=
  normSMulSelf_isCaratheodory.integral_nemyckii_sub_nemytskii_inner_memLp_sub_memLp_ge_of_ae_all_sub_inner_sub_ge_of_growth_of_holderConjugate_real
    example332
    MemLp.zero
    zero_le_one
    norm_normSMulSelf_le
    one_half_pos
    example_hfCp
    hu
    hv

example
    {u v : ℝ → ℝ^1}
    (huv : (fun ω : ℝ => normSMulSelf ω (u ω)) =ᵐ[μ1] (fun ω : ℝ => normSMulSelf ω (v ω))) :
    u =ᵐ[μ1] v :=
  ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge_real one_half_pos example_hfCp huv

example
    (u : ℝ → ℝ) :
    (eLpNorm (fun ω : ℝ => |u ω| * (u ω) + 1) 2 μ1) ^ 2 ≤
    2 * ((eLpNorm (↓1 : ℝ → ℝ) 2 μ1) ^ 2 + (eLpNorm u 4 μ1) ^ 4) := by
  by_cases fin_norm : eLpNorm (↓1 : ℝ → ℝ) 2 μ1 = ⊤
  · rw [fin_norm]
    simp
  · have h12 : MemLp (↓1 : ℝ → ℝ) 2 μ1 :=
      ⟨aestronglyMeasurable_const, lt_top_iff_ne_top.← fin_norm⟩
    have key :=
      eLpNorm_nemytskii_rpow_le_of_growth_real
        (by norm_num)
        (by norm_num)
        one_le_two
        (by norm_num)
        h12
        zero_le_one
        (absMulSelfAddOne_growth μ1)
        (fun ω : ℝ => realLIE (u ω))
    simp only [ENNReal.toReal_ofNat] at key
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_one, ENNReal.one_rpow, mul_one] at key
    simp only [absMulSelfAddOne_comp_realLIE, eLpNorm_realLIE] at key
    have h2 : ∀ x : ℝ≥0∞, x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
      intro
      rw [←ENNReal.rpow_natCast]
      norm_num
    have h4 : ∀ x : ℝ≥0∞, x ^ (4 : ℕ) = x ^ (4 : ℝ) := by
      intro
      rw [←ENNReal.rpow_natCast]
      norm_num
    simp only [h2, h4]
    rwa [mul_add]

example
    {uₙ : ℕ → ℝ → ℝ} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ1)
    {u : ℝ → ℝ} (h2u : MemLp u (2 : ℝ≥0∞) μ1)
    (huuₙ : TendstoInMeasure μ1 uₙ atTop u)
    (h2uₙ : UnifIntegrable uₙ (2 : ℝ≥0∞) μ1) :
    Tendsto
      (fun n : ℕ => eLpNorm (fun ω : ℝ => |uₙ n ω| * (uₙ n ω) - |u ω| * (u ω)) (1 : ℝ≥0∞) μ1)
      atTop (𝓝 0) :=
  have growth : ∀ᵐ ω ∂μ1, ∀ ξ : ℝ,
      |(fun (_ : ℝ) (x : ℝ) => |x| * x) ω ξ| ≤
      |(0 : ℝ → ℝ) ω| + (1 : ℝ) * |ξ| ^ ((2 : ℝ≥0∞) / (1 : ℝ≥0∞)).toReal := by
    filter_upwards with ω ξ
    have h2 : ((2 : ℝ≥0∞) / (1 : ℝ≥0∞)).toReal = 2 := by norm_num
    rw [h2, Real.rpow_two, pow_two]
    simp
  absMulSelf_caratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth
    one_le_two
    ENNReal.top_ne_ofNat.symm
    (le_refl 1)
    ENNReal.one_ne_top
    MemLp.zero
    zero_le_one
    growth
    huₙ
    h2u
    huuₙ
    h2uₙ

example
    {u : ℝ → ℝ} (hu : MemLp u 3 μ1) :
    MemLp (fun ω : ℝ => |u ω| * (u ω)) (3 / 2) μ1 ∧
    Integrable (fun ω : ℝ => ⟪ω + |u ω| * (u ω), u ω⟫) μ1 ∧
    ((eLpNorm u 3 μ1) ^ (3 : ℝ)).toReal * (2 / 3) - (eLpNorm ((2 / 3) * |·| ^ (3 / 2 : ℝ)) 1 μ1).toReal ≤
    ∫ ω : ℝ, ⟪ω + |u ω| * (u ω), u ω⟫ ∂μ1 := by
  have hu3 : MemLp u ↱(3 : ℝ) μ1 := by
    rwa [show (↱(3 : ℝ) : ℝ≥0∞) = 3 by norm_num]
  have h332 : Real.HolderConjugate 3 (3 / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  obtain ⟨hμ1, integ, bound⟩ :=
    coerciveF_caratheodory.integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth h332
      coercive_a_memLp zero_le_one coerciveF_growth
      coerciveB_integrable coerciveF_coercive (memLp_realLIE hu3)
  have huuμ1 :
      ∫ ω : ℝ, ⟪coerciveF ω (realLIE (u ω)), realLIE (u ω)⟫ ∂μ1 =
      ∫ ω : ℝ, ⟪ω + |u ω| * u ω, u ω⟫ ∂μ1 := by
    refine integral_congr_ae (Filter.Eventually.of_forall ↓?_)
    simp only [coerciveF_comp, realLIE.inner_map_map]
  constructor
  · have hu32 : MemLp (fun ω : ℝ => realLIE (ω + |u ω| * u ω)) ↱(3 / 2) μ1 := by
      simpa only [coerciveF_comp] using hμ1
    have huu :
        (fun ω : ℝ => ω + |u ω| * u ω) - id =
        (fun ω : ℝ => |u ω| * u ω) := by
      funext
      simp [add_sub_cancel_left]
    exact ofReal3div2 ▸ huu ▸ (memLp_of_realLIE hu32).sub coercive_a_memLp
  constructor
  · refine integ.congr (Filter.Eventually.of_forall ↓?_)
    simp only [coerciveF_comp, realLIE.inner_map_map]
  · have hu3 :
        ∫ ω : ℝ, ‖realLIE (u ω)‖ ^ (3 : ℝ) ∂μ1 =
        ∫ ω : ℝ, |u ω| ^ (3 : ℝ) ∂μ1 := by
      refine integral_congr_ae (Filter.Eventually.of_forall ↓?_)
      simp only [norm_realLIE]
    have hLHS :
        ((eLpNorm u 3 μ1) ^ (3 : ℝ)).toReal * (2 / 3)
            - (eLpNorm ((2 / 3) * |·| ^ (3 / 2 : ℝ)) 1 μ1).toReal
        = (2 / 3 : ℝ) * ∫ ω : ℝ, ‖realLIE (u ω)‖ ^ (3 : ℝ) ∂μ1
            - ∫ ω : ℝ, |coerciveB ω| ∂μ1 := by
      rw [hu3, integral_norm_cube_eq hu, integral_coerciveB_eq]
      show _ = _ - (eLpNorm ((2 / 3) * |·| ^ (3 / 2)) 1 μ1).toReal
      ring
    rw [←huuμ1, hLHS]
    exact bound

example {u : ℝ → ℝ} (hu : MemLp u 3 μ1) :
    MemLp (fun ω : ℝ => |u ω| * (u ω)) (3 / 2) μ1 := by
  simpa [absMulSelf, ofReal3div2] using
    absMulSelf_caratheodory.memLp_nemytskii_of_growth_of_holderConjugate
      example332
      MemLp.zero
      zero_le_one
      norm_absMulSelf_le
      (ENNReal.ofReal_ofNat 3 ▸ hu)

example
    {u : ℝ → ℝ} (hu : MemLp u 3 μ1)
    {v : ℝ → ℝ} (hv : MemLp v 3 μ1) :
    Integrable (fun ω : ℝ => ⟪|u ω| * (u ω) - |v ω| * (v ω), u ω - v ω⟫) μ1 := by
  simpa [absMulSelf] using
    absMulSelf_caratheodory.integrable_nemyckii_sub_nemytskii_inner_memLp_sub_memLp_of_growth_of_holderConjugate
      example332
      MemLp.zero
      zero_le_one
      norm_absMulSelf_le
      (ENNReal.ofReal_ofNat 3 ▸ hu)
      (ENNReal.ofReal_ofNat 3 ▸ hv)

example
    {u : ℝ → ℝ} (hu : MemLp u 3 μ1)
    {v : ℝ → ℝ} (hv : MemLp v 3 μ1) :
    Integrable
      (fun ω : ℝ => ⟪|u ω| * (u ω) - |v ω| * (v ω), u ω - v ω⟫) μ1 ∧
    ∫ ω : ℝ, ⟪|u ω| * (u ω) - |v ω| * (v ω), u ω - v ω⟫ ∂μ1 ≥
      (1 / 2 : ℝ) * ∫ ω : ℝ, |u ω - v ω| ^ (3 : ℝ) ∂μ1 := by
  simpa [absMulSelf] using
    absMulSelf_caratheodory.integral_nemyckii_sub_nemytskii_inner_memLp_sub_memLp_ge_of_ae_all_sub_inner_sub_ge_of_growth_of_holderConjugate
      example332
      MemLp.zero
      zero_le_one
      norm_absMulSelf_le
      one_half_pos
      absMulSelf_hfCp
      (ENNReal.ofReal_ofNat 3 ▸ hu)
      (ENNReal.ofReal_ofNat 3 ▸ hv)

example {u v : ℝ → ℝ}
    (huv : (fun ω : ℝ => |u ω| * (u ω)) =ᵐ[μ1] (fun ω : ℝ => |v ω| * (v ω))) :
    u =ᵐ[μ1] v := by
  apply ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge one_half_pos absMulSelf_hfCp
  simpa [absMulSelf] using huv
