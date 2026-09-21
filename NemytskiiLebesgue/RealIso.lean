import UtilitiesZCU.Basic

open MeasureTheory
open scoped ENNReal

noncomputable def realLIE : ℝ ≃ₗᵢ[ℝ] ℝ^1 where
  toLinearEquiv :=
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
  norm_map' := by
    intro
    rw [EuclideanSpace.norm_eq]
    simp [WithLp.linearEquiv, LinearEquiv.funUnique, Real.sqrt_sq_eq_abs]

@[simp]
lemma norm_realLIE (r : ℝ) : ‖realLIE r‖ = |r| := realLIE.norm_map r

lemma realLIE_mul (c s : ℝ) : realLIE (c * s) = c • realLIE s := by
  rw [←smul_eq_mul, map_smul]

lemma normSMulSelf_realLIE {T : Type} (t : T) (s : ℝ) :
    normSMulSelf t (realLIE s) = realLIE (|s| * s) := by
  rw [normSMulSelf, norm_realLIE, ←smul_eq_mul, map_smul]

lemma eLpNorm_realLIE {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (u : Ω → ℝ) :
    eLpNorm (fun ω : Ω => realLIE (u ω)) p μ = eLpNorm u p μ := by
  rw [←eLpNorm_norm (fun ω : Ω => realLIE (u ω)), ←eLpNorm_norm u]
  simp

lemma memLp_realLIE {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} {u : Ω → ℝ} (hu : MemLp u p μ) :
    MemLp (fun ω : Ω => realLIE (u ω)) p μ :=
  hu.continuousLinearMap_comp realLIE.toLinearEquiv.toContinuousLinearMap
