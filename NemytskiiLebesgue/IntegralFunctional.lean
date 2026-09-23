import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.Frechet
import NemytskiiLebesgue.Nemytskii
import NemytskiiLebesgue.RealIso

open MeasureTheory
open scoped ENNReal

theorem Function.IsCaratheodory.integralFunctional_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ := by
  rw [←memLp_one_iff_integrable]
  exact
    hf.memLp_nemytskii_of_growth
      h1p
      hp
      le_rfl
      ENNReal.one_ne_top
      (memLp_one_iff_integrable.← ha)
      hC
      ((div_one p).symm ▸ hfaCp)
      hup

theorem Function.IsCaratheodory.integralFunctional_wellDefined_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : f.IsCaratheodory μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ :=
  hf.integralFunctional_wellDefined h1p hp.ne_top ha hC hfaCp hup

-- begin all private (unfortunately breaks the notation)

noncomputable def Function.outR1 {Ω : Type*} {m : ℕ} (f : Ω → ℝ^m → ℝ) :
    Ω → ℝ^m → ℝ^1 :=
  (realLIE <| f · ·)

noncomputable def Function.outR1nested {Ω : Type*} {m : ℕ} (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) :
    Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^1) :=
  (realLIE.toContinuousLinearMap.comp <| f' · ·)

lemma Function.IsCaratheodory.outR1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : f.IsCaratheodory μ) :
    f.outR1.IsCaratheodory μ :=
  hf.comp_continuous realLIE.continuous

lemma Function.IsCaratheodory.outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : f'.IsCaratheodory μ) :
    f'.outR1nested.IsCaratheodory μ :=
  hf'.comp_continuous (by fun_prop)

lemma hasFDerivAt_outR1_outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)}
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f.outR1 ω) (f'.outR1nested ω ξ) ξ :=
  hff'.mono ↓(fun _ => realLIE.toContinuousLinearMap.hasFDerivAt.comp _ <| · _)

lemma Function.outR1nested_norm_eq
    {Ω : Type*}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) (ω : Ω) (ξ : ℝ^m) :
    ‖f'.outR1nested ω ξ‖ = ‖f' ω ξ‖ := by
  have f'_norm : ∀ v : ℝ^m, ‖realLIE.toContinuousLinearMap (f' ω ξ v)‖ = ‖f' ω ξ v‖ := by
    bound
  refine'
    le_antisymm
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg (f' ω ξ)) fun v : ℝ^m => _)
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg (f'.outR1nested ω ξ)) fun v : ℝ^m => _)
  · exact f'_norm v ▸ ContinuousLinearMap.le_opNorm ..
  · exact le_trans (f'_norm v).ge ((realLIE.toContinuousLinearMap.comp (f' ω ξ)).le_opNorm v)

lemma Function.outR1nested_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ))
    {b : Ω → ℝ} {C α : ℝ}
    (hf'bCα : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f'.outR1nested ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α := by
  filter_upwards [hf'bCα] with ω hω ξ using le_trans (by rw [Function.outR1nested_norm_eq]) (hω ξ)

-- end all private

lemma Function.IsCaratheodory.memLp_nemytskii_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : f'.IsCaratheodory μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfbCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ :=
  have hp : 1 ≤ p :=
    hpq.lt.le
  have hq : 1 ≤ q :=
    hpq.symm.lt.le
  memLp_nemytskii_of_growth_of_aestronglyMeasurable
    (zero_lt_one.trans_le (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hp))
    ENNReal.ofReal_ne_top
    (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hq)
    ENNReal.ofReal_ne_top
    hbq
    hC
    (by
      simp_all [ENNReal.toReal_div]
      show ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ |b ω| + C * ‖ξ‖ ^ ((↱p).toReal / (↱q).toReal)
      filter_upwards [hfbCp] with ω hω ξ using
        le_trans
          (hω ξ)
          (add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) le_rfl (by linarith)) hC))
        |> le_trans <| by simp [hpq.div_conj_eq_sub_one,
            ENNReal.toReal_ofReal (zero_le_one.trans hp),
            ENNReal.toReal_ofReal (zero_le_one.trans hq)]
    )
    hup
    (hf'.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)

lemma Function.IsCaratheodory.integrable_nemytskii_deriv_apply
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : f'.IsCaratheodory μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ := by
  have f'_u_in_Lq : MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ := by
    apply_rules [memLp_nemytskii_deriv]
  have integrabl : Integrable (fun ω : Ω => ‖f' ω (u ω)‖ * ‖v ω‖) μ := by
    convert! f'_u_in_Lq.norm.integrable_mul hvp.norm using 1
    exact hpq.symm.ennrealOfReal
  apply integrabl.mono'
  · have cont : Continuous (fun p : (ℝ^m →L[ℝ] ℝ) × ℝ^m => p.fst p.snd) := by
      fun_prop
    exact cont.comp_aestronglyMeasurable (f'_u_in_Lq.left.prodMk hvp.left)
  · exact Filter.Eventually.of_forall ↓(ContinuousLinearMap.le_opNorm _ _)

lemma norm_integral_le_eLpNorm_one_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : Ω → ℝ) :
    ‖∫ ω : Ω, g ω ∂μ‖ ≤ (eLpNorm g 1 μ).toReal := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal] <;> norm_num
  convert! norm_integral_le_lintegral_norm g using 1
  norm_num [Real.enorm_eq_ofReal_abs]

theorem Function.IsCaratheodory.integralFunctional_frechet_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : f.IsCaratheodory μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : f'.IsCaratheodory μ)
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    (∀ v : Ω → ℝ^m, MemLp v ↱p μ →
      Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          ‖∫ ω : Ω, (f ω (u ω + l ω) - f ω (u ω) - (f' ω (u ω)) (l ω)) ∂μ‖ ≤
            ε * (eLpNorm l ↱p μ).toReal) := by
  constructor
  · exact ↓(hf'.integrable_nemytskii_deriv_apply hpq hbq hC.le hf'bCp hup)
  · have nemytskii_bound : ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
        MemLp l ↱p μ → eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => f.outR1 ω (u ω + l ω) - f.outR1 ω (u ω) - f'.outR1nested ω (u ω) (l ω)) ↱(1 : ℝ) μ ≤
          ↱ε * eLpNorm l ↱p μ := by
      apply hf.outR1.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm hf'.outR1nested (hasFDerivAt_outR1_outR1nested hff') hpq.lt.le hpq.symm.lt.le hpq.symm h0b hbq hC _ hup
      rw [hpq.div_conj_eq_sub_one]
      exact f'.outR1nested_growth hf'bCp
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := nemytskii_bound ε hε
    use δ, hδ
    intro l hl hl'
    have key := hbound l hl hl'
    apply le_trans (norm_integral_le_eLpNorm_one_toReal _)
    convert! ENNReal.toReal_mono _ key using 1
    · norm_num [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      congr! 2
      ext
      simp [Function.outR1, Function.outR1nested, realLIE, ENorm.enorm, ←NNReal.coe_inj, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hl.eLpNorm_ne_top)
