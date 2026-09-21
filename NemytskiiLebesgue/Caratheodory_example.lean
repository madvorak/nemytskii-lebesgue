import NemytskiiLebesgue.Closure
import NemytskiiLebesgue.RealIso

open MeasureTheory

section irrelevant

private noncomputable def aux7pos (Ω : Type) :
    Ω → (⊤ : Set ℝ^1).Elem → ℝ^1 :=
  ↓(fun y : (⊤ : Set ℝ^1).Elem => realLIE (‖y.val‖ ^ 7 * (realLIE.symm y.val)⁺))

private lemma aux7pos_isCaratheodory
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) :
    (aux7pos Ω).IsCaratheodory μ :=
  Function.IsCaratheodory.of_continuous <|
    realLIE.continuous.comp <|
      (continuous_subtype_val.norm.pow 7).mul <|
        continuous_posPart.comp (realLIE.symm.continuous.comp continuous_subtype_val)

end irrelevant

example {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : Ω → ℝ} (hu : AEMeasurable u μ) :
    AEMeasurable (fun ω : Ω => |u ω| ^ 7 * (u ω)⁺) μ := by
  have hu' : AEMeasurable
      (fun ω : Ω => (⟨realLIE (u ω), Set.mem_univ _⟩ : (Set.univ : Set ℝ^1))) μ :=
    (realLIE.continuous.measurable.comp_aemeasurable hu).subtype_mk
  have h7u := (aux7pos_isCaratheodory μ).aeMeas_nemytskii_of_aeMeas_real hu'
  have h7Ω :
      (fun ω : Ω => aux7pos Ω ω ⟨realLIE (u ω), Set.mem_univ _⟩) =
      (fun ω : Ω => realLIE (|u ω| ^ 7 * (u ω)⁺)) := by
    funext ω
    simp [aux7pos]
  rw [h7Ω] at h7u
  exact realLIE.symm.continuous.measurable.comp_aemeasurable h7u
