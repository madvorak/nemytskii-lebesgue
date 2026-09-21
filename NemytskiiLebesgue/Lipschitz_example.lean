import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.Lipschitz
import NemytskiiLebesgue.RealIso

open MeasureTheory
open scoped ENNReal

variable {Ω : Type}

private noncomputable def reluVec : Ω → ℝ^1 → ℝ^1 :=
  ↓(fun x : ℝ^1 => WithLp.toLp 2 ↓((x.ofLp 0)⁺))

private lemma reluVec_zero (ω : Ω) : reluVec ω (0 : ℝ^1) = 0 := by
  ext
  simp [reluVec]

private lemma reluVec_lipschitz (ω : Ω) (ξ η : ℝ^1) :
    ‖reluVec ω ξ - reluVec ω η‖ ≤ (1 : ℝ) * ‖ξ - η‖ := by
  simp [reluVec, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply posPart_sub_posPart_sq_le

private lemma normSMulSelf_growth (ω : Ω) (ξ η : ℝ^1) :
    ‖normSMulSelf ω ξ - normSMulSelf ω η‖ ≤ 1 * (1 + ‖ξ‖ ^ (1 : ℝ) + ‖η‖ ^ (1 : ℝ)) * ‖ξ - η‖ := by
  have triangle_ineq : ‖‖ξ‖ • ξ - ‖η‖ • η‖ ≤ ‖ξ‖ * ‖ξ - η‖ + |‖ξ‖ - ‖η‖| * ‖η‖ := by
    convert norm_add_le (‖ξ‖ • (ξ - η)) ((‖ξ‖ - ‖η‖) • η) using 1
    · apply congr_arg
      ext
      simp
      ring
    · simp [norm_smul]
  norm_num
  exact triangle_ineq.trans (by nlinarith [abs_norm_sub_norm_le ξ η, norm_nonneg (ξ - η), norm_nonneg ξ, norm_nonneg η])

variable [MeasurableSpace Ω] {μ : Measure Ω}

private lemma reluVec_isCaratheodory : reluVec.IsCaratheodory μ :=
  Function.IsCaratheodory.of_continuous (by fun_prop)

private lemma reluVec_memLp_top_one : MemLp (fun _ : Ω => (1 : ℝ)) ⊤ μ :=
  memLp_top_const 1

private lemma reluVec_memLp_zero : MemLp (fun ω : Ω => reluVec ω 0) 2 μ :=
  have h0 : (fun ω : Ω => reluVec ω 0) = (0 : Ω → ℝ^1) := by
    funext ω
    simpa using reluVec_zero ω
  h0 ▸ MemLp.zero

example {u : Ω → ℝ^1} (hu : MemLp u 2 μ) :
    MemLp (fun ω : Ω => reluVec ω (u ω)) 2 μ :=
  reluVec_isCaratheodory.memLp_nemytskii_of_globally_lipschitz
    one_le_two
    reluVec_memLp_zero
    hu
    reluVec_memLp_top_one
    (Filter.Eventually.of_forall reluVec_lipschitz)

example {u v : Ω → ℝ^1}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    eLpNorm (fun ω : Ω => reluVec ω (u ω) - reluVec ω (v ω)) 2 μ ≤ eLpNorm ↓(1 : ℝ) ⊤ μ * eLpNorm (u - v) 2 μ :=
  eLpNorm_nemytskii_sub_nemytskii_le_eLpNorm_mul_eLpNorm_of_globally_lipschitz_real
    reluVec_memLp_top_one.aemeasurable
    (Filter.Eventually.of_forall reluVec_lipschitz)
    hu
    hv

example [IsFiniteMeasure μ] (R : ℝ) (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → ℝ,
        MemLp u 2 μ →
        MemLp v 2 μ →
        eLpNorm u 2 μ ≤ ↱R →
        eLpNorm v 2 μ ≤ ↱R →
        eLpNorm (fun ω : Ω => |u ω| * (u ω) - |v ω| * (v ω)) 1 μ ≤ ↱L * eLpNorm (u - v) 2 μ := by
  have h2 : ↱2 = 2 := by
    norm_num
  obtain ⟨L, hL, HL⟩ :=
    locally_eLpNorm_nemytskii_sub_nemytskii_le_ofReal_mul_eLpNorm_sub_of_ae_all_all_norm_sub_le_real
      (μ := μ)
      one_le_two
      (le_refl 1)
      zero_le_one
      (by norm_num)
      zero_lt_one
      (Filter.Eventually.of_forall normSMulSelf_growth)
      hR
  refine ⟨L, hL, fun u v hu hv huR hvR => ?_⟩
  have key :=
    HL
      (fun ω : Ω => realLIE (u ω))
      (fun ω : Ω => realLIE (v ω))
      (memLp_realLIE (h2 ▸ hu))
      (memLp_realLIE (h2 ▸ hv))
      (eLpNorm_realLIE u ▸ h2 ▸ huR)
      (eLpNorm_realLIE v ▸ h2 ▸ hvR)
  have hlhs :
      (fun ω : Ω => normSMulSelf ω (realLIE (u ω)) - normSMulSelf ω (realLIE (v ω))) =
      (fun ω : Ω => realLIE (|u ω| * (u ω) - |v ω| * (v ω))) := by
    funext
    rw [normSMulSelf_realLIE, normSMulSelf_realLIE, ←map_sub]
  rw [hlhs, eLpNorm_realLIE] at key
  have hrhs :
      eLpNorm ((fun ω : Ω => realLIE (u ω)) - (fun ω : Ω => realLIE (v ω))) ↱2 μ =
      eLpNorm (u - v) ↱2 μ := by
    have huv :
        (fun ω : Ω => realLIE (u ω)) - (fun ω : Ω => realLIE (v ω)) =
        (fun ω : Ω => realLIE ((u - v) ω)) := by
      funext
      simp [Pi.sub_apply, map_sub]
    rw [huv, eLpNorm_realLIE]
  rw [hrhs, h2] at key
  convert key
  norm_num
