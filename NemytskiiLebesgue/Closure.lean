import NemytskiiLebesgue.Caratheodory

open MeasureTheory Filter

theorem Function.IsCaratheodory.const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    (c : F) :
    Function.IsCaratheodory (fun _ : Ω => fun _ : D => c) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓continuous_const

theorem Function.IsCaratheodory.of_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → F} (hf : StronglyMeasurable f) :
    Function.IsCaratheodory (fun ω : Ω => fun _ : D => f ω) μ where
  isStronglyMeasurable _ := hf
  ae_continuous := Eventually.of_forall ↓continuous_const

theorem Function.IsCaratheodory.of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : D → F} (hf : Continuous f) :
    Function.IsCaratheodory (fun _ : Ω => fun x : D => f x) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓hf

theorem Function.IsCaratheodory.add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Add F] [ContinuousAdd F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f + g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).add (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.add hgω

theorem Function.IsCaratheodory.real_add
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ^k} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f + g) μ :=
  hf.add hg

theorem Function.IsCaratheodory.neg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Neg F] [ContinuousNeg F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (-f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).neg
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.neg

theorem Function.IsCaratheodory.sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Sub F] [ContinuousSub F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f - g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).sub (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.sub hgω

theorem Function.IsCaratheodory.real_sub
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ^k} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f - g) μ :=
  hf.sub hg

theorem Function.IsCaratheodory.mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Mul F] [ContinuousMul F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f * g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).mul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.mul hgω

theorem Function.IsCaratheodory.real_mul
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f * g) μ :=
  hf.mul hg

theorem Function.IsCaratheodory.smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*} [TopologicalSpace M]
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousSMul M F]
    {f : Ω → D → M} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f • g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).smul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.smul hgω

theorem Function.IsCaratheodory.const_smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*}
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousConstSMul M F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) (c : M) :
    Function.IsCaratheodory (c • f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).const_smul c
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.const_smul c

theorem Function.IsCaratheodory.inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Inv F] [ContinuousInv F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (f⁻¹) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).inv
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.inv

theorem Function.IsCaratheodory.div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Div F] [ContinuousDiv F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f / g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).div' (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.div' hgω

theorem Function.IsCaratheodory.real_div
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ} (hg : g.IsCaratheodory μ)
    (hg0 : ∀ᵐ ω ∂μ, ∀ x : D, g ω x ≠ 0) :
    Function.IsCaratheodory (f / g) μ where
  isStronglyMeasurable x :=
    ((hf.isStronglyMeasurable x).measurable.div
      (hg.isStronglyMeasurable x).measurable).stronglyMeasurable
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous, hg0] with ω hcf hcg hne
    exact hcf.div hcg hne

theorem Function.IsCaratheodory.pow_nat
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Monoid F] [ContinuousMul F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) (n : ℕ) :
    Function.IsCaratheodory (f ^ n) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).pow n
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.pow n

theorem Function.IsCaratheodory.real_pow_nat
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : f.IsCaratheodory μ) (n : ℕ) :
    Function.IsCaratheodory (f ^ n) μ :=
  hf.pow_nat n

theorem Function.IsCaratheodory.sup
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Max F] [ContinuousSup F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f ⊔ g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).sup (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.sup hgω

theorem Function.IsCaratheodory.real_sup
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f ⊔ g) μ :=
  hf.sup hg

theorem Function.IsCaratheodory.inf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Min F] [ContinuousInf F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → F} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f ⊓ g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).inf (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.inf hgω

theorem Function.IsCaratheodory.real_inf
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : f.IsCaratheodory μ)
    {g : Ω → D → ℝ} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (f ⊓ g) μ :=
  hf.inf hg

theorem Function.IsCaratheodory.comp_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : F → G} (hg : Continuous g) :
    Function.IsCaratheodory (g <| f · ·) μ where
  isStronglyMeasurable x :=
    hg.comp_stronglyMeasurable (hf.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hg.comp hω

theorem Function.IsCaratheodory.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω' → Ω} (hg : MeasurePreserving g μ' μ) :
    Function.IsCaratheodory (f ∘ g) μ' where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).comp_measurable hg.measurable
  ae_continuous :=
    hg.quasiMeasurePreserving.ae hf.ae_continuous

theorem Function.IsCaratheodory.norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (‖f · ·‖) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).norm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.norm

theorem Function.IsCaratheodory.nnnorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (‖f · ·‖₊) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).nnnorm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.nnnorm

theorem Function.IsCaratheodory.prod
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : f.IsCaratheodory μ)
    {g : Ω → D → G} (hg : g.IsCaratheodory μ) :
    Function.IsCaratheodory (fun ω : Ω => fun x : D => (f ω x, g ω x)) μ where
  isStronglyMeasurable x :=
    StronglyMeasurable.prodMk
      (hf.isStronglyMeasurable x)
      (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact Continuous.prodMk hfω hgω

theorem Function.IsCaratheodory.fst
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).fst) μ :=
  hf.comp_continuous continuous_fst

theorem Function.IsCaratheodory.snd
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : f.IsCaratheodory μ) :
    Function.IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).snd) μ :=
  hf.comp_continuous continuous_snd
