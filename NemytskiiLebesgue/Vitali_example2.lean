import NemytskiiLebesgue.Vitali

open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace Topology Matrix

private noncomputable def stdBaseVec (n : ℕ) (i : ℕ) : ℝ^n :=
  if h : i < n then EuclideanSpace.single (⟨i, h⟩ : Fin n) 1 else 0

private noncomputable def sineMatrixField (n : ℕ) (x : ℝ^n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n => Real.sin (((i : ℝ) + 1 + ((j : ℝ) + 1)) / ‖x‖))

private noncomputable def combinedNonlinearity (n : ℕ) (α : ℝ) (x ξ : ℝ^n) :
    ℝ^n :=
  ‖x‖ ^ (-α) • stdBaseVec n 0 +
    (EuclideanSpace.equiv (Fin n) ℝ).symm (sineMatrixField n x *ᵥ (fun j : Fin n => ξ j * |ξ j|))

private noncomputable def radialProfile (n : ℕ) (γ : ℝ) (x : ℝ^n) :
    ℝ^n :=
  (‖x‖ ^ (-γ)) • stdBaseVec n 1

private noncomputable def perturbSeq (n : ℕ) (j : ℕ) (x : ℝ^n) :
    ℝ^n :=
  (Metric.ball 0 (1 / (j : ℝ))).indicator ↓(((j : ℝ) ^ ((n : ℝ) / 8)) • stdBaseVec n (n - 1)) x

private noncomputable def approxSeq (n : ℕ) (γ : ℝ) (j : ℕ) (x : ℝ^n) :
    ℝ^n :=
  radialProfile n γ x + perturbSeq n j x

private noncomputable def ball1 (n : ℕ) : Measure ℝ^n :=
  volume.restrict (Metric.ball 0 1)

private instance (n : ℕ) : IsFiniteMeasure (ball1 n) := by
  constructor
  rw [ball1, Measure.restrict_apply_univ]
  exact measure_ball_lt_top

private lemma norm_e {n : ℕ} {i : ℕ} (h : i < n) : ‖stdBaseVec n i‖ = 1 := by
  unfold stdBaseVec
  aesop

private lemma integrableOn_norm_rpow_ball {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : -(n : ℝ) < s) :
    IntegrableOn (fun x : ℝ^n => ‖x‖ ^ s) (Metric.ball 0 1) volume := by
  have integrable_norm_rpow_ball_iff :
      IntegrableOn (fun x : ℝ^n => ‖x‖ ^ s) (Metric.ball 0 1) volume ↔
      IntegrableOn (fun y : ℝ => y ^ (n - 1) * y ^ s) (Set.Ioo (0 : ℝ) 1) volume := by
    have integrable_ball_iff_indicator_aux :
        IntegrableOn (fun x : ℝ^n => ‖x‖ ^ s) (Metric.ball 0 1) volume ↔
        IntegrableOn (fun x : ℝ^n => ‖x‖ ^ s * ((Metric.ball 0 1).indicator ↓1 x)) ⊤ volume := by
      simp only [Set.top_eq_univ, integrableOn_univ]
      rw [←MeasureTheory.integrable_indicator_iff measurableSet_ball]
      congr! 1
      ext
      simp [Set.indicator]
    have integrable_indicator_iff_real_aux :
        IntegrableOn (fun x : ℝ^n => ‖x‖ ^ s * ((Metric.ball 0 1).indicator ↓1 x)) ⊤ volume ↔
        IntegrableOn (fun y : ℝ => y ^ (n - 1) * y ^ s * (if y < 1 then 1 else 0)) (Set.Ioi 0) volume := by
      convert MeasureTheory.integrable_fun_norm_addHaar (E := ℝ^n) volume (f := fun y => y ^ s * (if y < 1 then 1 else 0)) using 1
      · simp [Set.indicator, Metric.mem_ball]
      · norm_num [mul_assoc, mul_comm, mul_left_comm, Module.finrank_self]
      · exact ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, ne_of_apply_ne (· ⟨0, hn⟩) (by norm_num)⟩
    convert integrable_indicator_iff_real_aux using 1
    rw [←MeasureTheory.integrable_indicator_iff measurableSet_Ioo,
        ←MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
    congr! 1
    ext
    simp only [Set.indicator, Set.mem_Ioo, Set.mem_Ioi, mul_ite, mul_one, mul_zero]
    split_ifs <;> tauto
  rw [integrable_norm_rpow_ball_iff]
  have integrable_rpow_Ioo : IntegrableOn (fun y : ℝ => y ^ ((n - 1 : ℝ) + s)) (Set.Ioo 0 1) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).left.mono_set (Set.Ioo_subset_Ioc_self)
  refine integrable_rpow_Ioo.congr_fun (fun x hx => ?_) measurableSet_Ioo
  rw [←Real.rpow_natCast, ←Real.rpow_add hx.left]
  cases n <;> aesop

private lemma memLp_norm_rpow_neg_ball {n : ℕ} (hn : 1 ≤ n) {β : ℝ}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (hlt : β * p.toReal < n) :
    MemLp (‖·‖ ^ (-β)) p (ball1 n) := by
  have integrable : IntegrableOn (fun x : ℝ^n => ‖x‖ ^ (-(β * p.toReal))) (Metric.ball 0 1) volume := by
    convert integrableOn_norm_rpow_ball hn _ using 1
    linarith
  · rw [←integrable_norm_rpow_iff _ hp0 hp]
    apply integrable.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), ←Real.rpow_mul (norm_nonneg x)]
    ring_nf
    exact Measurable.aestronglyMeasurable (Measurable.pow_const (measurable_norm) (-β))

private lemma combinedNonlinearity_caratheodory (n : ℕ) (α : ℝ) : (combinedNonlinearity n α).IsCaratheodory (ball1 n) := by
  constructor
  · refine ↓(Measurable.stronglyMeasurable ?_)
    simp only [combinedNonlinearity, sineMatrixField, PiLp.continuousLinearEquiv_symm_apply]
    apply Measurable.add
    · exact Measurable.smul (Measurable.pow_const (measurable_norm) _) measurable_const
    · refine Measurable.comp (?_ : Measurable (WithLp.toLp 2)) ?_
      · fun_prop
      · rw [measurable_pi_iff]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        fun_prop (disch := norm_num)
  · filter_upwards
    unfold combinedNonlinearity
    fun_prop

private lemma combinedNonlinearity_growth {n : ℕ} (hn : 1 ≤ n) (α : ℝ) :
    ∀ᵐ x ∂(ball1 n), ∀ ξ : ℝ^n,
      ‖combinedNonlinearity n α x ξ‖ ≤ |‖x‖ ^ (-α)| + Real.sqrt n * ‖ξ‖ ^ (2 : ℝ) := by
  refine' Filter.Eventually.of_forall _
  intro x ξ
  have hnξ2 :
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm (sineMatrixField n x *ᵥ (fun j : Fin n => ξ j * |ξ j|))‖
      ≤ Real.sqrt n * ‖ξ‖ ^ 2 := by
    have amat_norm : ∀ i : Fin n, ∀ j : Fin n, |sineMatrixField n x i j| ≤ 1 :=
      ↓↓(Real.abs_sin_le_one _)
    have amat_norm_comp :
        ∀ i : Fin n, |(sineMatrixField n x *ᵥ (fun j : Fin n => ξ j * |ξ j|)) i| ≤ ‖ξ‖ ^ 2 := by
      intro i
      have sum : |∑ j : Fin n, sineMatrixField n x i j * (ξ j * |ξ j|)| ≤ ∑ j : Fin n, |ξ j| ^ 2 := by
        apply le_trans (Finset.abs_sum_le_sum_abs _ _)
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        refine le_trans ?_ (mul_le_of_le_one_left (sq_nonneg |ξ.ofLp j|) (amat_norm i j))
        cases abs_cases (ξ.ofLp j) <;> simp only [abs_mul, abs_abs, abs_mul_abs_self, sq_abs] <;> nlinarith
      convert! sum using 1
      norm_num [EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _]
    simp_all only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
      PiLp.continuousLinearEquiv_symm_apply, Real.sqrt_le_iff]
    rw [mul_pow, Real.sq_sqrt <| Nat.cast_nonneg _]
    constructor
    · positivity
    · refine le_trans
          (Finset.sum_le_sum ↓↓(show (_ : ℝ) ^ 2 ≤
            (Real.sqrt (∑ x : Fin n, ξ.ofLp x ^ 2) ^ 2) ^ 2 from ?_)) ?_
      · nlinarith only [abs_le.→ (amat_norm_comp ‹_›)]
      · norm_num
  apply le_trans (norm_add_le _ _)
  rw [norm_smul, Real.norm_eq_abs, norm_e]
  · norm_num [hn]
    exact hnξ2
  · linarith

private lemma memLp_aFun {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : α < (n : ℝ) / 2) :
    MemLp (‖·‖ ^ (-α)) 2 (ball1 n) := by
  convert memLp_norm_rpow_neg_ball hn two_ne_zero (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num) _ using 1
  rw [ENNReal.toReal_ofNat]
  linarith

private lemma memLp_radialProfile {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ : γ < (n : ℝ) / 4) :
    MemLp (radialProfile n γ) 4 (ball1 n) := by
  have memLp : MemLp (‖·‖ ^ (-γ)) 4 (ball1 n) := by
    refine memLp_norm_rpow_neg_ball hn
      (show (4 : ℝ≥0∞) ≠ 0 by norm_num)
      (show (4 : ℝ≥0∞) ≠ ⊤ by norm_num)
      ?_
    erw [ENNReal.toReal_ofNat]
    linarith
  have lipschitz : LipschitzWith ⟨‖stdBaseVec n 1‖, norm_nonneg _⟩ (fun y : ℝ => y • stdBaseVec n 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    norm_num [dist_eq_norm, ←sub_smul, mul_comm, norm_smul]
    rfl
  exact lipschitz.comp_memLp (by norm_num) memLp

private lemma memLp_perturbSeq (n : ℕ) (j : ℕ) : MemLp (perturbSeq n j) 4 (ball1 n) := by
  convert! MeasureTheory.MemLp.indicator _ _ using 1
  · exact measurableSet_ball
  · apply memLp_const

private lemma memLp_approxSeq {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ : γ < (n : ℝ) / 4) (j : ℕ) :
    MemLp (approxSeq n γ j) 4 (ball1 n) :=
  (memLp_radialProfile hn hγ).add (memLp_perturbSeq n j)

private lemma approxSeq_sub_radialProfile (n : ℕ) (γ : ℝ) (j : ℕ) :
    approxSeq n γ j - radialProfile n γ = perturbSeq n j := by
  ext
  simp [approxSeq]

private lemma eLpNorm_perturbSeq_tendsto_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun j : ℕ => eLpNorm (perturbSeq n j) 4 (ball1 n)) atTop (𝓝 0) := by
  have indicator :
      ∀ j : ℕ, j ≥ 1 →
        eLpNorm (perturbSeq n j) 4 (ball1 n) =
        ↱((1 : ℝ) ^ (-(n : ℝ) / 4) * (j : ℝ) ^ (-(n : ℝ) / 8) *
          (ENNReal.toReal ((ball1 n) (Metric.ball 0 1))) ^ (1 / 4 : ℝ)) := by
    intro j hj
    have indicator :
        eLpNorm (perturbSeq n j) 4 (ball1 n) =
        ↱((j : ℝ) ^ ((n : ℝ) / 8) *
          (ENNReal.toReal (ball1 n (Metric.ball 0 (1 / (j : ℝ)))) ^ (1 / 4 : ℝ))) := by
      convert! eLpNorm_indicator_const
        (show MeasurableSet (Metric.ball (0 : ℝ^n) (1 / (j : ℝ))) from measurableSet_ball)
          (show (4 : ℝ≥0∞) ≠ 0 by norm_num) (show (4 : ℝ≥0∞) ≠ ⊤ by norm_num) using 1
      rw [←ENNReal.toReal_eq_toReal_iff'] <;> norm_num
      · rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_e] <;> norm_num
        · rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_rpow]
        · linarith
      · refine ENNReal.mul_ne_top ?_ ?_ <;> norm_num [ENNReal.rpow_eq_top_iff]
    have ball :
        (ball1 n) (Metric.ball 0 (1 / (j : ℝ))) =
        ↱((1 / (j : ℝ)) ^ n) * (ball1 n) (Metric.ball 0 1) := by
      convert MeasureTheory.Measure.addHaar_ball
        (volume : Measure ℝ^n) (0 : ℝ^n) (by positivity : (0 : ℝ) ≤ 1 / (j : ℝ)) using 1
      · norm_num [ball1]
        rw [MeasureTheory.Measure.restrict_apply']
        · rw [Set.inter_eq_left.← (Metric.ball_subset_ball <| inv_le_one_of_one_le₀ <| mod_cast hj)]
        · exact measurableSet_ball
      · norm_num [ball1]
      · exact ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, ne_of_apply_ne (· ⟨0, hn⟩) (by norm_num)⟩
    simp_all only [ge_iff_le, one_div, inv_pow, ENNReal.toReal_mul, inv_nonneg, Nat.cast_nonneg,
      pow_nonneg, ENNReal.toReal_ofReal, Real.one_rpow, one_mul]
    rw [Real.mul_rpow _ _, Real.inv_rpow _, ←Real.rpow_natCast,
      ←Real.rpow_mul _, ←Real.rpow_neg _] <;> try positivity
    ring_nf
    rw [←Real.rpow_add (by positivity)]
    ring_nf
  have hn80 : Filter.Tendsto (fun j : ℕ => (j : ℝ) ^ (-(n : ℝ) / 8)) Filter.atTop (nhds 0) := by
    have hn8 : (0 : ℝ) < ↑n / 8 := by finiteness
    convert (tendsto_rpow_neg_atTop hn8).comp tendsto_natCast_atTop_atTop
    grind
  rw [Filter.tendsto_congr' (by
    filter_upwards [Filter.eventually_ge_atTop 1] with j hj
    rw [indicator j hj])]
  convert ENNReal.tendsto_ofReal ((hn80.const_mul _).mul_const _) using 1
  norm_num

private lemma approxSeq_tendsto_radialProfile {n : ℕ} (hn : 1 ≤ n) (γ : ℝ) :
    Tendsto (fun j : ℕ => eLpNorm (approxSeq n γ j - radialProfile n γ) 4 (ball1 n)) atTop (𝓝 0) := by
  simp only [approxSeq_sub_radialProfile]
  exact eLpNorm_perturbSeq_tendsto_zero hn

private theorem nemytskii_L2_convergence {n : ℕ} (hn : 2 ≤ n) {α γ : ℝ}
    (hα : 0 < α ∧ α < (n : ℝ) / 2)
    (hγ : 0 < γ ∧ γ < (n : ℝ) / 8) :
    (fun j : ℕ => fun x : ℝ^n => combinedNonlinearity n α x (approxSeq n γ j x)).ConvergesTo
      (fun x : ℝ^n => combinedNonlinearity n α x (radialProfile n γ x)) 2 (ball1 n) :=
  have hn1 : 1 ≤ n := by omega
  have hγ4 : γ < (n : ℝ) / 4 := by
    linarith [hγ.right]
  have hfaCpq : ∀ᵐ x ∂(ball1 n), ∀ ξ : ℝ^n,
      ‖combinedNonlinearity n α x ξ‖ ≤
      |‖x‖ ^ (-α)| + Real.sqrt n * ‖ξ‖ ^ (((4 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal) := by
    convert combinedNonlinearity_growth hn1 α
    norm_num
  have hLp := approxSeq_tendsto_radialProfile hn1 γ
  have huim : TendstoInMeasure (ball1 n) (approxSeq n γ) atTop (radialProfile n γ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (memLp_approxSeq hn1 hγ4 ·|>.aestronglyMeasurable)
      (memLp_radialProfile hn1 hγ4).aestronglyMeasurable hLp
  have huui : UnifIntegrable (approxSeq n γ) 4 (ball1 n) :=
    unifIntegrable_of_tendsto_Lp one_le_four ENNReal.top_ne_ofNat.symm
      (memLp_approxSeq hn1 hγ4) (memLp_radialProfile hn1 hγ4) hLp
  (combinedNonlinearity_caratheodory n α).seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
    one_le_four ENNReal.ofNat_lt_top one_le_two ENNReal.ofNat_lt_top
    (memLp_aFun hn1 hα.right) (Real.sqrt_nonneg _) hfaCpq
    (memLp_approxSeq hn1 hγ4 ·|>.aestronglyMeasurable.aemeasurable)
    (memLp_radialProfile hn1 hγ4) huim huui

private lemma memLp_combinedNonlinearity_comp {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : α < (n : ℝ) / 2)
    {w : ℝ^n → ℝ^n} (hw : MemLp w 4 (ball1 n)) :
    MemLp (fun x : ℝ^n => combinedNonlinearity n α x (w x)) 2 (ball1 n) :=
  have hfaCpq : ∀ᵐ x ∂(ball1 n), ∀ ξ : ℝ^n,
      ‖combinedNonlinearity n α x ξ‖ ≤
      |‖x‖ ^ (-α)| + Real.sqrt n * ‖ξ‖ ^ ((4 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
    rw [show (((4 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal) = (2 : ℝ) by norm_num]
    exact combinedNonlinearity_growth hn α
  (combinedNonlinearity_caratheodory n α).memLp_nemytskii_of_growth_real
    one_le_four ENNReal.ofNat_lt_top one_le_two ENNReal.ofNat_lt_top
    (memLp_aFun hn hα) (Real.sqrt_nonneg _) hfaCpq hw

private lemma integral_norm_sq_eq {n : ℕ}
    {h : ℝ^n → ℝ^n} (hmem : MemLp h 2 (ball1 n)) :
    (∫ x : ℝ^n, ‖h x‖ ^ 2 ∂(ball1 n)) = (eLpNorm h 2 (ball1 n)).toReal ^ 2 := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · convert (MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _) using 1
    · rw [←ENNReal.toReal_pow, ←ENNReal.rpow_natCast, ←ENNReal.rpow_mul]
      norm_num
    · exact Filter.Eventually.of_forall (sq_nonneg ‖h ·‖)
    · exact (hmem.left.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  · norm_num
  · norm_num

example {n : ℕ} (hn : 2 ≤ n) {α γ : ℝ}
    (hα : 0 < α ∧ α < (n : ℝ) / 2)
    (hγ : 0 < γ ∧ γ < (n : ℝ) / 8) :
    Tendsto
      (fun j : ℕ => ∫ x : ℝ^n,
        ‖combinedNonlinearity n α x (approxSeq n γ j x) - combinedNonlinearity n α x (radialProfile n γ x)‖ ^ 2 ∂(ball1 n))
      atTop
      (𝓝 0) := by
  have hn1 : 1 ≤ n := by omega
  have hγ4 : γ < (n : ℝ) / 4 := by
    have h0 : (0 : ℝ) ≤ n := by positivity
    have : (n : ℝ) / 8 ≤ (n : ℝ) / 4 := by linarith
    linarith [hγ.right]
  have hL2 := nemytskii_L2_convergence hn hα hγ
  have hmem_lim : MemLp (fun x : ℝ^n => combinedNonlinearity n α x (radialProfile n γ x)) 2 (ball1 n) :=
    memLp_combinedNonlinearity_comp hn1 hα.right (memLp_radialProfile hn1 hγ4)
  have hdiff : ∀ j : ℕ,
      MemLp
        ((fun x : ℝ^n => combinedNonlinearity n α x (approxSeq n γ j x)) -
         (fun x : ℝ^n => combinedNonlinearity n α x (radialProfile n γ x)))
        2
        (ball1 n) :=
    fun j : ℕ => (memLp_combinedNonlinearity_comp hn1 hα.right (memLp_approxSeq hn1 hγ4 j)).sub hmem_lim
  have key : ∀ j : ℕ,
      (∫ x : ℝ^n,
        ‖combinedNonlinearity n α x (approxSeq n γ j x) - combinedNonlinearity n α x (radialProfile n γ x)‖ ^ 2 ∂(ball1 n)) =
      (eLpNorm
        ((fun x : ℝ^n => combinedNonlinearity n α x (approxSeq n γ j x)) -
         (fun x : ℝ^n => combinedNonlinearity n α x (radialProfile n γ x)))
        2
        (ball1 n)
      ).toReal ^ 2 := by
    intro j
    rw [←integral_norm_sq_eq (hdiff j)]
    simp
  have hreal : Tendsto
      (fun j : ℕ => (eLpNorm
        ((fun x : ℝ^n => combinedNonlinearity n α x (approxSeq n γ j x)) -
         (fun x : ℝ^n => combinedNonlinearity n α x (radialProfile n γ x)))
        2
        (ball1 n)
      ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hL2
    finiteness
  simpa using (hreal.pow 2).congr (fun j : ℕ => (key j).symm)
