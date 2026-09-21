import NemytskiiLebesgue.ConverseImplication

open MeasureTheory
open scoped NNReal ENNReal

private noncomputable def coeff : ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) 1).indicator (· ^ (-(1 : ℝ) / 4))

private noncomputable def singularNonlinearity : ℝ → ℝ^1 → ℝ^1 :=
  fun x : ℝ =>
    (coeff x • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) + normSMulSelf x ·)

private theorem coeff_memLp_one : MemLp coeff 1 volume := by
  have hCoeffIntegrable :
      IntegrableOn (· ^ (-(1 : ℝ) / 4)) (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).left.mono_set Set.Ioo_subset_Ioc_self
  rw [memLp_one_iff_integrable]
  rwa [←integrable_indicator_iff] at hCoeffIntegrable
  norm_num

private theorem singularNonlinearity_isCaratheodory : singularNonlinearity.IsCaratheodory volume :=
  ⟨↓(StronglyMeasurable.add
    (((measurable_id.pow_const _).indicator measurableSet_Ioo).smul_const _).stronglyMeasurable
    (Continuous.stronglyMeasurable (by continuity))),
  Filter.Eventually.of_forall
    ↓(Continuous.add continuous_const (continuous_norm.smul continuous_id))⟩

private theorem nemytskii_memLp (u : ℝ → ℝ^1) (hu : MemLp u 2 volume) :
    MemLp (fun x : ℝ => singularNonlinearity x (u x)) 1 volume := by
  apply MemLp.add
  · apply MemLp.mono' coeff_memLp_one.norm
    · exact (((measurable_id.pow_const _).indicator measurableSet_Ioo).smul_const _).aestronglyMeasurable
    · norm_num [norm_smul]
  · exact
      (normSMulSelf_isCaratheodory.memLp_nemytskii_of_growth_real
        one_le_two
        ENNReal.ofNat_lt_top
        (le_refl 1)
        ENNReal.one_lt_top
        MemLp.zero zero_le_one
        (by norm_num [normSMulSelf, sq, norm_smul])
      ) hu

private theorem growth_bound :
    ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^1,
      ‖singularNonlinearity x ξ‖ ≤ |coeff x| + 1 * ‖ξ‖ ^ (((2 : ℝ≥0∞) / (1 : ℝ≥0∞)).toReal) := by
  apply Filter.Eventually.of_forall
  intro x ξ
  simp only [singularNonlinearity, Fin.isValue, div_one, ENNReal.toReal_ofNat, Real.rpow_ofNat, one_mul]
  convert! norm_add_le (coeff x • (EuclideanSpace.single 0 1)) (‖ξ‖ • ξ) using 1
  norm_num [norm_smul, Real.sqrt_sq_eq_abs]
  ring_nf

example :
    ∃ a : ℝ → ℝ, MemLp a 1 volume ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^1,
        ‖singularNonlinearity x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (((2 : ℝ≥0∞) / (1 : ℝ≥0∞)).toReal) :=
  (singularNonlinearity_isCaratheodory.memLp_nemytskii_volume_iff_growth one_le_two (by norm_num) (le_refl 1) ENNReal.one_lt_top).→
    nemytskii_memLp

example (u : ℝ → ℝ^1) (hu : MemLp u 2 volume) :
    MemLp (fun x : ℝ => singularNonlinearity x (u x)) 1 volume :=
  (singularNonlinearity_isCaratheodory.memLp_nemytskii_volume_iff_growth one_le_two (by norm_num) (le_refl 1) ENNReal.one_lt_top).←
    ⟨coeff, coeff_memLp_one, 1, zero_le_one, growth_bound⟩
    u hu
