import NemytskiiLebesgue.Continuity

open MeasureTheory
open scoped NNReal ENNReal

lemma memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (h1p : 1 ≤ p)
    {f : Ω → D → F} (hf0p : MemLp (f · 0) p μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable ((fun ω : Ω => f ω (u ω))) μ)
    {L : Ω → ℝ} (hL : AEStronglyMeasurable L μ) (hL' : eLpNorm L ⊤ μ < ⊤)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ := by
  have eLpNorm_f : eLpNorm (fun ω : Ω => ‖f ω 0‖ + L ω * ‖u ω‖) p μ < ⊤ := by
    refine' lt_of_le_of_lt (eLpNorm_add_le ..) (ENNReal.add_lt_top.← ⟨_, _⟩)
    · exact hf0p.left.norm
    · exact hL.mul hup.left.norm
    · exact h1p
    · simpa using hf0p.right
    · have eLpNorm_L_u : eLpNorm (fun ω : Ω => L ω * ‖u ω‖) p μ ≤ eLpNorm L ∞ μ * eLpNorm (‖u ·‖) p μ := by
        convert eLpNorm_smul_le_mul_eLpNorm hL hup.aestronglyMeasurable.norm using 1
        congr! 1
        rotate_left
        · apply mul_comm
        · constructor
          aesop
        · ext
          apply mul_comm
      exact lt_of_le_of_lt eLpNorm_L_u (ENNReal.mul_lt_top hL' (by simpa using hup.right))
  refine' ⟨hfu, lt_of_le_of_lt (eLpNorm_mono_ae _) eLpNorm_f⟩
  filter_upwards [hfL] with ω hω
  have := hω (u ω) 0
  simp_all
  cases abs_cases (‖f ω 0‖ + L ω * ‖u ω‖) <;> linarith [norm_sub_norm_le (f ω (u ω)) (f ω 0)]

theorem Function.IsCaratheodory.memLp_nemytskii_of_globally_lipschitz
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : f.IsCaratheodory μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hf0p : MemLp (f · 0) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {L : Ω → ℝ} (hL : MemLp L ⊤ μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ :=
  memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
    h1p
    hf0p
    hup
    (hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.left)
    hL.left
    hL.right
    hfL

theorem eLpNorm_nemytskii_sub_nemytskii_le_eLpNorm_mul_eLpNorm_of_globally_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {L : Ω → ℝ} (hL : AEStronglyMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {u v : Ω → D} (huv : AEStronglyMeasurable (u - v) μ)
    (p : ℝ≥0∞) :
    eLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ := by
  calc eLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ
    ≤ eLpNorm (L • fun ω : Ω => ‖u ω - v ω‖) p μ := by
        apply eLpNorm_mono_ae
        filter_upwards [hfL] with ω hω
        show ‖f ω (u ω) - f ω (v ω)‖ ≤ ‖(L • fun ω : Ω => ‖u ω - v ω‖) ω‖
        exact le_trans (hω _ _) (le_abs_self _)
  _ ≤ eLpNorm L ⊤ μ * eLpNorm (fun ω : Ω => ‖u ω - v ω‖) p μ :=
        eLpNorm_smul_le_mul_eLpNorm huv.norm hL
  _ = eLpNorm L ⊤ μ * eLpNorm (u - v) p μ := by
        congr 1
        exact eLpNorm_norm (u - v)

theorem eLpNorm_nemytskii_sub_nemytskii_le_eLpNorm_mul_eLpNorm_of_globally_lipschitz_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {L : Ω → ℝ} (hL : AEMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {p : ℝ≥0∞}
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v p μ) :
    eLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ :=
  eLpNorm_nemytskii_sub_nemytskii_le_eLpNorm_mul_eLpNorm_of_globally_lipschitz hL.aestronglyMeasurable hfL (hup.left.sub hvp.left) p

lemma ennreal_holderTriple_of_lt_of_lt
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    ENNReal.HolderTriple ↱(p / α) ↱p ↱(p / (α + 1)) := by
  constructor
  rw [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_div_of_pos] <;> try positivity
  rw [←ENNReal.toReal_eq_toReal_iff'] <;> norm_num
  · rw [ENNReal.toReal_add] <;> norm_num [hp, hα]
    rw [ENNReal.toReal_ofReal hα.le,
        ENNReal.toReal_ofReal hp.le,
        ENNReal.toReal_ofReal (by positivity)]
    ring
  · grind
  · exact RCLike.ofReal_pos.→ hp

private lemma aestronglyMeas_mul_one_add_norm_rpow_add_norm_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {u : Ω → D} (hu : AEStronglyMeasurable u μ)
    {v : Ω → D} (hv : AEStronglyMeasurable v μ)
    (C α : ℝ) :
    AEStronglyMeasurable (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α)) μ :=
  AEStronglyMeasurable.const_mul
    (AEStronglyMeasurable.add
      (AEStronglyMeasurable.add aestronglyMeasurable_const
        (hu.norm.aemeasurable.pow_const α).aestronglyMeasurable)
        (hv.norm.aemeasurable.pow_const α).aestronglyMeasurable)
    _

lemma eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    eLpNorm ↓(1 : ℝ) ↱(p / α) μ = (μ ⊤) ^ (α / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal] <;> norm_num [hp, hα, div_eq_mul_inv]
  rw [ENNReal.toReal_ofReal (by positivity), inv_eq_one_div, div_eq_mul_inv]
  norm_num [mul_comm]

private lemma eLpNorm_one_add_norm_rpow_add_norm_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p α : ℝ} (h1p : 1 ≤ p) (hα : 0 < α) (hpα : α ≤ p)
    {D : Type*} [NormedAddCommGroup D]
    {u : Ω → D} (hu : AEStronglyMeasurable u μ)
    {v : Ω → D} (hv : AEStronglyMeasurable v μ)
    {R : ℝ} (hR : 0 < R)
    (huR : eLpNorm u ↱p μ ≤ ↱R)
    (hvR : eLpNorm v ↱p μ ≤ ↱R) :
    eLpNorm (fun ω : Ω => (1 : ℝ) + ‖u ω‖ ^ α + ‖v ω‖ ^ α) ↱(p / α) μ ≤ ↱((μ ⊤).toReal ^ (α / p) + 2 * R ^ α) := by
  have triangle :
      eLpNorm (fun ω : Ω => 1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α) ↱(p / α) μ ≤
      eLpNorm ↓(1 : ℝ) ↱(p / α) μ +
      eLpNorm (‖u ·‖ ^ α) ↱(p / α) μ +
      eLpNorm (‖v ·‖ ^ α) ↱(p / α) μ := by
    refine' le_trans _ (add_le_add (eLpNorm_add_le ..) le_rfl)
    · convert! eLpNorm_add_le ..
      · exact AEStronglyMeasurable.add (aestronglyMeasurable_const) (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable
      · exact (hv.norm.aemeasurable.pow_const _).aestronglyMeasurable
      · rw [ENNReal.le_ofReal_iff_toReal_le] <;> norm_num <;> nlinarith [mul_div_cancel₀ p hα.ne']
    · exact aestronglyMeasurable_const
    · exact (hu.norm.aemeasurable.pow_const _).aestronglyMeasurable
    · exact ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hα] ; linarith)
  by_cases hμ : μ ⊤ = 0 <;> simp_all [two_mul]
  convert triangle.trans _ using 1
  have h0p : 0 < p := zero_lt_one.trans_le h1p
  convert
    add_le_add_three
      (eLpNorm_one_ofReal_eq_measure_univ_rpow_inv μ h0p hα).le
      (rpow_le_ofReal_rpow_of_le_ofReal hα.le hR huR)
      (rpow_le_ofReal_rpow_of_le_ofReal hα.le hR hvR)
      using 1
  · rw [eLpNorm_norm_rpow_div_eq u hα h0p,
        eLpNorm_norm_rpow_div_eq v hα h0p]
  · show ↱((μ ⊤).toReal ^ (α / p) + (R ^ α + R ^ α)) = μ ⊤ ^ (α / p) + ↱(R ^ α) + ↱(R ^ α)
    rw [ENNReal.ofReal_add,
        ENNReal.ofReal_add,
        ←ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    ring
    all_goals positivity

theorem locally_eLpNorm_nemytskii_sub_nemytskii_le_ofReal_mul_eLpNorm_sub_of_ae_all_all_norm_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ} (h1p : 1 ≤ p)
    {q : ℝ} (h1q : 1 ≤ q)
    {α : ℝ} (hα : 0 ≤ α)
    (hqpα : q = p / (α + 1))
    {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ C * (1 + ‖ξ‖ ^ α + ‖η‖ ^ α) * ‖ξ - η‖)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → D,
        MemLp u ↱p μ →
        MemLp v ↱p μ →
        eLpNorm u ↱p μ ≤ ↱R →
        eLpNorm v ↱p μ ≤ ↱R →
        eLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) ↱q μ ≤ ↱L * eLpNorm (u - v) ↱p μ := by
  by_cases α_pos : 0 < α
  · refine'
      ⟨C * ((μ ⊤).toReal ^ (α / p) + 2 * R ^ α),
       mul_pos hC
        (add_pos_of_nonneg_of_pos
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (mul_pos zero_lt_two (Real.rpow_pos_of_pos hR α))),
       fun u v hu hv huR hvR => _⟩
    have holder : eLpNorm (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α) * ‖u ω - v ω‖) ↱q μ ≤
                  eLpNorm (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α)) ↱(p / α) μ * eLpNorm (fun ω : Ω => ‖u ω - v ω‖) ↱p μ := by
      have holde :
        ∀ g l : Ω → ℝ,
          AEStronglyMeasurable g μ → AEStronglyMeasurable l μ →
            eLpNorm (fun ω : Ω => g ω * l ω) ↱q μ ≤ eLpNorm g ↱(p / α) μ * eLpNorm l ↱p μ := by
        intros g l hg hl
        convert! eLpNorm_smul_le_mul_eLpNorm hl hg using 1
        convert ennreal_holderTriple_of_lt_of_lt (by positivity) α_pos using 1
        rw [hqpα]
      apply holde
      · apply aestronglyMeas_mul_one_add_norm_rpow_add_norm_rpow hu.left hv.left
      · exact (hu.left.sub hv.left).norm
    refine' le_trans (eLpNorm_mono_ae _) (holder.trans _)
    · filter_upwards [hfC] with ω hω using le_trans (hω _ _) (le_abs_self _)
    · gcongr
      · convert!
          mul_le_mul_right
            (eLpNorm_one_add_norm_rpow_add_norm_rpow_le h1p α_pos
              (show α ≤ p by
                rw [hqpα] at h1q
                rw [le_div_iff₀] at h1q <;> nlinarith
              ) hu.left hv.left hR huR hvR
            ) ↱C using 1
        · simp [eLpNorm, eLpNorm', ENNReal.mul_rpow_of_nonneg, Real.enorm_of_nonneg hC.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)),
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ←ENNReal.rpow_mul,
              mul_inv_cancel₀ (ne_of_gt (ENNReal.toReal_pos (by positivity) (by simp))),
              ENNReal.rpow_one]
        · rw [ENNReal.ofReal_mul hC.le]
      · simp [eLpNorm]
        rfl
  · refine' ⟨3 * C, by positivity, _⟩
    intro u v hu hv huR hvR
    have hα0 : α = 0 := eq_of_le_of_ge (Std.not_lt.→ α_pos) hα
    have h3C : ∀ᵐ ω : Ω ∂μ, ‖f ω (u ω) - f ω (v ω)‖ ≤ 3 * C * ‖u ω - v ω‖ := by
      filter_upwards [hfC] with ω hω using le_trans (hω (u ω) (v ω)) (by
        norm_num [hα0]
        nlinarith [norm_nonneg (u ω - v ω)])
    have hqp : q = p
    · rw [hqpα, hα0]
      norm_num
    exact hqp ▸ eLpNorm_le_mul_eLpNorm_of_ae_le_mul h3C ↱p

theorem locally_eLpNorm_nemytskii_sub_nemytskii_le_ofReal_mul_eLpNorm_sub_of_ae_all_all_norm_sub_le_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ} (h1p : 1 ≤ p)
    {q : ℝ} (h1q : 1 ≤ q)
    {α : ℝ} (hα : 0 ≤ α)
    (hqpα : q = p / (α + 1))
    {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ C * (1 + ‖ξ‖ ^ α + ‖η‖ ^ α) * ‖ξ - η‖)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → ℝ^m,
        MemLp u ↱p μ →
        MemLp v ↱p μ →
        eLpNorm u ↱p μ ≤ ↱R →
        eLpNorm v ↱p μ ≤ ↱R →
        eLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) ↱q μ ≤ ↱L * eLpNorm (u - v) ↱p μ :=
  locally_eLpNorm_nemytskii_sub_nemytskii_le_ofReal_mul_eLpNorm_sub_of_ae_all_all_norm_sub_le h1p h1q hα hqpα hC hfC hR
