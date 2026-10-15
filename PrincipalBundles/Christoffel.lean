/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import PrincipalBundles.FrameBundle

/-!
# Christoffel symbols as a gauge transformation (Schuller, Example 22.7)

A chart on `M` gives a local section of the frame bundle, the coordinate frame
`(∂/∂x¹, …, ∂/∂xⁿ)`. We read a frame at `m` as a map `E → T_mM`, so the coordinate frame of the
chart at `b` is the inverse of the tangent trivialisation at `b`.

For the coordinate frames `σ₁, σ₂` of the charts at `b₁` (coordinates `x`) and `b₂`
(coordinates `y`), the gauge map with `σ₁ <• Ω = σ₂` is the Jacobian

  `Ω = D(x ∘ y⁻¹)` at `y(m)`, i.e. `Ωⁱⱼ = ∂xⁱ/∂yʲ`.

Schuller writes `Ωⁱⱼ = ∂yⁱ/∂xʲ`; with frames acting on the right by composition, as here, the
roles of `x` and `y` are exchanged. Feeding the coordinate frames into
`frameBundleYangMills_transformation` gives

  `Γ_y(v) = Ω⁻¹ Γ_x(v) Ω + Ω⁻¹ dΩ(v)`,

which in components, with `v = ∂/∂y^ν`, is

  `Γ'ⁱⱼν = (∂yⁱ/∂xᵏ) Γᵏₗμ (∂xˡ/∂yʲ) (∂x^μ/∂y^ν) + (∂yⁱ/∂xᵏ) ∂²xᵏ/∂y^ν∂yʲ`.

## Main definitions

* `coordFrameMap I b m`: the coordinate frame of the chart at `b`, at `m`, as an endomorphism of
  the model space.
* `coordFrame I b`: the coordinate frame section of the frame bundle.
* `coordGauge I b₁ b₂`: the change of coordinate frame, `σ₁ <• coordGauge I b₁ b₂ = σ₂`.

## Main statements

* `isLocalSection_coordFrame`: a coordinate frame is a local section over its chart domain.
* `coordFrame_smul_coordGauge`: `σ₁ <• Ω = σ₂` on the overlap.
* `coe_coordGauge`: `Ω` is the Jacobian `D(x ∘ y⁻¹)` at `y(m)`.
* `coe_coordGauge_inv`: `Ω⁻¹` is the Jacobian the other way round.
* `christoffel_transformation`: the transformation law.
* `mfderiv_coordGauge`: without boundary, `dΩ(v)` is the second derivative
  `D²(x ∘ y⁻¹)(y m) (Dy v)`.
* `christoffel_transformation_chart`: the transformation law with `Ω`, `Ω⁻¹` and `dΩ` written
  as derivatives of the chart transitions.
* `christoffel_components`: for `M` modelled on `Fin n → ℝ`, the law in components,
  `Γ'ⁱⱼν = Σ (∂yⁱ/∂xᵏ) Γᵏₗμ (∂xˡ/∂yʲ) (∂x^μ/∂y^ν) + Σ (∂yⁱ/∂xᵏ) ∂²xᵏ/∂y^ν∂yʲ`.
-/

open Bundle Set ContinuousLinearMap RightActions
open scoped Manifold Topology Bundle ContDiff

noncomputable section

section CoordinateFrames

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open Classical in
/-- The coordinate frame of the chart at `b`, at the point `m`: the inverse of the tangent
trivialisation at `b`, read as an endomorphism of `E` (recall `T_mM = E`). Off the chart domain
we take the identity, which is still a frame; its value there plays no role. -/
def coordFrameMap (b m : M) : E →L[ℝ] E :=
  if m ∈ (chartAt H b).source then
    @id (E →L[ℝ] E) ((trivializationAt E (TangentSpace I) b).symmL ℝ m)
  else 1

variable {I} in
lemma coordFrameMap_of_mem {b m : M} (hm : m ∈ (chartAt H b).source) :
    coordFrameMap I b m = @id (E →L[ℝ] E) ((trivializationAt E (TangentSpace I) b).symmL ℝ m) := by
  simp only [coordFrameMap, hm, ↓reduceIte]

/-- `coordFrameMap` typed as a section of the Hom bundle, so that terms built from it are
well-typed at the `implicit` transparency `rw` uses (`TangentSpace I m` and `E` carry
different instances syntactically). -/
def coordFrameSection (b : M) : (m : M) → (Bundle.Trivial M E m →L[ℝ] TangentSpace I m) :=
  fun m => coordFrameMap I b m

lemma isUnit_coordFrameMap (b m : M) : IsUnit (coordFrameMap I b m) := by
  by_cases hm : m ∈ (chartAt H b).source
  · rw [coordFrameMap_of_mem hm]
    have hb : m ∈ (trivializationAt E (TangentSpace I) b).baseSet := hm
    refine ⟨⟨@id (E →L[ℝ] E) ((trivializationAt E (TangentSpace I) b).symmL ℝ m),
      @id (E →L[ℝ] E) ((trivializationAt E (TangentSpace I) b).continuousLinearMapAt ℝ m),
      ?_, ?_⟩, rfl⟩
    · ext y
      exact (trivializationAt E (TangentSpace I) b).symmL_continuousLinearMapAt hb y
    · ext y
      exact (trivializationAt E (TangentSpace I) b).continuousLinearMapAt_symmL hb y
  · simp only [coordFrameMap, hm, ↓reduceIte]
    exact isUnit_one

/-- The coordinate frame section of the frame bundle induced by the chart at `b`. -/
def coordFrame (b : M) : M → ↥(FrameBundle I M) := fun m =>
  ⟨⟨m, coordFrameSection I b m⟩, isUnit_coordFrameMap I b m⟩

/-- The change of coordinate frame from the chart at `b₁` to the chart at `b₂`: the tangent
coordinate change from the trivialisation at `b₂` to the one at `b₁`. -/
def coordGauge (b₁ b₂ m : M) : (E →L[ℝ] E)ˣ :=
  ((trivializationAt E (TangentSpace I) b₂).coordChangeL ℝ
    (trivializationAt E (TangentSpace I) b₁) m).toUnit

variable {I}

/-- `τ₁⁻¹ ∘ (τ₁ ∘ τ₂⁻¹) = τ₂⁻¹` on the overlap. -/
theorem symmL_coordChangeL (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) (y : E) :
    (trivializationAt E (TangentSpace I) b₁).symmL ℝ m
        ((trivializationAt E (TangentSpace I) b₂).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) b₁) m y) =
      (trivializationAt E (TangentSpace I) b₂).symmL ℝ m y := by
  have h₁ : m ∈ (trivializationAt E (TangentSpace I) b₁).baseSet := hm.1
  have h₂ : m ∈ (trivializationAt E (TangentSpace I) b₂).baseSet := hm.2
  rw [Trivialization.coordChangeL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂)
      (trivializationAt E (TangentSpace I) b₁) ⟨h₂, h₁⟩,
    Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₁) h₁,
    Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂) h₂,
    Trivialization.symm_apply_apply_mk (trivializationAt E (TangentSpace I) b₁) h₁]

/-- On the overlap of the two chart domains, `σ₁ <• Ω = σ₂`. -/
theorem coordFrame_smul_coordGauge (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) :
    coordFrame I b₁ m <• coordGauge I b₁ b₂ m = coordFrame I b₂ m := by
  have h₁ : m ∈ (trivializationAt E (TangentSpace I) b₁).baseSet := hm.1
  have h₂ : m ∈ (trivializationAt E (TangentSpace I) b₂).baseSet := hm.2
  apply Subtype.ext
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    ext y
    -- the frame of `σ₁ <• Ω` is `σ₁ ∘ Ω`
    change coordFrameMap I b₁ m (((coordGauge I b₁ b₂ m : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) y) =
      coordFrameMap I b₂ m y
    rw [coordFrameMap_of_mem hm.1, coordFrameMap_of_mem hm.2]
    change (trivializationAt E (TangentSpace I) b₁).symmL ℝ m
        ((trivializationAt E (TangentSpace I) b₂).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) b₁) m y) =
      (trivializationAt E (TangentSpace I) b₂).symmL ℝ m y
    rw [Trivialization.coordChangeL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂)
        (trivializationAt E (TangentSpace I) b₁) ⟨h₂, h₁⟩,
      Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₁) h₁,
      Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂) h₂,
      Trivialization.symm_apply_apply_mk (trivializationAt E (TangentSpace I) b₁) h₁]

/-- A coordinate frame is a local section of the frame bundle over its chart domain. -/
theorem isLocalSection_coordFrame (b : M) :
    IsLocalSection (IB := I) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (proj := frameBundleProj) (coordFrame I b) (chartAt H b).source := by
  refine ⟨(chartAt H b).open_source, ?_, fun m _ => rfl⟩
  intro m₀ hm₀
  apply ContMDiffAt.contMDiffWithinAt
  -- smoothness into the open subset `FrameBundle I M` of the Hom bundle is smoothness there
  refine (ContMDiffAt.subtypeVal_comp_iff (FrameBundle I M) (coordFrame I b) m₀).mp ?_
  change ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun m => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) m
      (coordFrameSection I b m)) m₀
  rw [contMDiffAt_section]
  -- in the Hom trivialisation at `m₀` the coordinate of the section is the tangent coordinate
  -- change from the trivialisation at `b` to the one at `m₀`, which is smooth
  have hU : (chartAt H b).source ∩ (chartAt H m₀).source ∈ 𝓝 m₀ :=
    ((chartAt H b).open_source.inter (chartAt H m₀).open_source).mem_nhds
      ⟨hm₀, mem_chart_source H m₀⟩
  have hsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun m => ((trivializationAt E (TangentSpace I) b).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) m₀) m : E →L[ℝ] E)) m₀ :=
    (contMDiffOn_coordChangeL (trivializationAt E (TangentSpace I) b)
      (trivializationAt E (TangentSpace I) m₀)).contMDiffAt hU
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hU] with m hm
  have hb : m ∈ (trivializationAt E (TangentSpace I) b).baseSet := hm.1
  have h₀ : m ∈ (trivializationAt E (TangentSpace I) m₀).baseSet := hm.2
  change (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) m₀
      ⟨m, coordFrameSection I b m⟩).2 =
    ((trivializationAt E (TangentSpace I) b).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) m₀) m : E →L[ℝ] E)
  rw [hom_trivializationAt_snd_eq m₀ ⟨m, coordFrameSection I b m⟩ h₀]
  ext y
  -- `τ₀ (σ y) = τ₀ (τ_b⁻¹ y)`, which is the coordinate change applied to `y`
  have hs : coordFrameMap I b m y = (trivializationAt E (TangentSpace I) b).symm m y := by
    rw [coordFrameMap_of_mem hm.1]
    exact Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b) hb y
  exact (congrArg (fun w => ((trivializationAt E (TangentSpace I) m₀) ⟨m, w⟩).2) hs).trans
    (Trivialization.coordChangeL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b)
      (trivializationAt E (TangentSpace I) m₀) ⟨hb, h₀⟩ y).symm

/-- The change of coordinate frame is the Jacobian of the chart transition:
`Ω = D(x ∘ y⁻¹)` at `y(m)`, where `x` is the chart at `b₁` and `y` the chart at `b₂`. -/
theorem coe_coordGauge (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) :
    ((coordGauge I b₁ b₂ m : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) =
      fderivWithin ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm) (range I)
        (extChartAt I b₂ m) := by
  have h₁ : m ∈ (trivializationAt E (TangentSpace I) b₁).baseSet := hm.1
  have h₂ : m ∈ (trivializationAt E (TangentSpace I) b₂).baseSet := hm.2
  rw [← tangentBundleCore_coordChange_achart]
  ext y
  change (trivializationAt E (TangentSpace I) b₂).coordChangeL ℝ
    (trivializationAt E (TangentSpace I) b₁) m y = _
  -- `τ₁ ∘ τ₂⁻¹`, then each factor as a coordinate change of `tangentBundleCore`
  rw [Trivialization.coordChangeL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂)
      (trivializationAt E (TangentSpace I) b₁) ⟨h₂, h₁⟩,
    ← Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) b₂) h₂,
    ← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) b₁) h₁,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hm.1,
    TangentBundle.symmL_trivializationAt_eq_core hm.2]
  exact (tangentBundleCore I M).coordChange_comp (achart H b₂) (achart H m) (achart H b₁) m
    ⟨⟨hm.2, mem_chart_source H m⟩, hm.1⟩ y

/-- The inverse change of coordinate frame is the change of coordinate frame the other way
round, hence the Jacobian `D(y ∘ x⁻¹)` at `x(m)`. -/
theorem coe_coordGauge_inv (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) :
    (((coordGauge I b₁ b₂ m)⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) =
      ((coordGauge I b₂ b₁ m : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) := by
  change (((trivializationAt E (TangentSpace I) b₂).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b₁) m).symm : E →L[ℝ] E) =
    ((trivializationAt E (TangentSpace I) b₁).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b₂) m : E →L[ℝ] E)
  rw [Trivialization.symm_coordChangeL (R := ℝ) (trivializationAt E (TangentSpace I) b₂)
    (trivializationAt E (TangentSpace I) b₁) ⟨hm.1, hm.2⟩]

end CoordinateFrames

section ChristoffelTransformation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Christoffel transformation law** (Schuller, Example 22.7).

For the coordinate frames of the charts at `b₁` (coordinates `x`) and `b₂` (coordinates `y`),
the local connection forms `Γ_x = σ_x^* ω` and `Γ_y = σ_y^* ω` are related on the overlap by

  `Γ_y(v) = Ω⁻¹ Γ_x(v) Ω + Ω⁻¹ dΩ(v)`,

where `Ω = coordGauge I b₁ b₂` is the Jacobian `D(x ∘ y⁻¹)` (`coe_coordGauge`) and `Ω⁻¹` is
`D(y ∘ x⁻¹)` (`coe_coordGauge_inv`). -/
theorem christoffel_transformation
    [SmoothRightGAction ∞ (modelWithCornersSelf ℝ (E →L[ℝ] E))
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) (E →L[ℝ] E)ˣ ↑(FrameBundle I M)]
    (τ : ConnectionForm (G := (E →L[ℝ] E)ˣ) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (IB := I) (P := ↑(FrameBundle I M)))
    (b₁ b₂ m : M) (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source)
    (v : TangentSpace I m) :
    yangMillsField τ (coordFrame I b₂) m v =
      (coordGauge I b₁ b₂ m)⁻¹.val ∘L (yangMillsField τ (coordFrame I b₁) m v) ∘L
        (coordGauge I b₁ b₂ m).val +
      (coordGauge I b₁ b₂ m)⁻¹.val ∘L
        (mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] E)) (coordGauge I b₁ b₂) m v) :=
  frameBundleYangMills_transformation τ (coordFrame I b₁) (coordFrame I b₂)
    (chartAt H b₁).source (chartAt H b₂).source
    (isLocalSection_coordFrame b₁) (isLocalSection_coordFrame b₂)
    (coordGauge I b₁ b₂) (fun m hm => coordFrame_smul_coordGauge b₁ b₂ m hm) m hm v

end ChristoffelTransformation

/-! ### The derivative of the gauge map is a second derivative

Without boundary, `fderivWithin` on `range I` is `fderiv`, and the derivative of
`m ↦ D(x ∘ y⁻¹)(y m)` is `D²(x ∘ y⁻¹)(y m)` applied to `Dy`. -/

section SecondDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Without boundary, the change of coordinate frame is `fderiv` of the chart transition. -/
theorem coe_coordGauge_of_boundaryless (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) :
    ((coordGauge I b₁ b₂ m : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) =
      fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm) (extChartAt I b₂ m) := by
  rw [coe_coordGauge b₁ b₂ m hm, I.range_eq_univ, fderivWithin_univ]

/-- The chart transition `x ∘ y⁻¹` is smooth near `y m`. -/
theorem contDiffAt_extChartAt_transition (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) :
    ContDiffAt ℝ ∞ (extChartAt I b₁ ∘ (extChartAt I b₂).symm) (extChartAt I b₂ m) := by
  have hm₂ : m ∈ (extChartAt I b₂).source := by rw [extChartAt_source]; exact hm.2
  apply (contDiffOn_ext_coord_change b₁ b₂).contDiffAt
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  exact Filter.inter_mem (extChartAt_target_mem_nhds' ((extChartAt I b₂).map_source hm₂))
    (extChartAt_preimage_mem_nhds' hm₂
      (by rw [extChartAt_source]; exact (chartAt H b₁).open_source.mem_nhds hm.1))

/-- The derivative of the change of coordinate frame is the second derivative of the chart
transition: `dΩ_m(v) = D²(x ∘ y⁻¹)(y m) (Dy_m v)`. -/
theorem mfderiv_coordGauge (b₁ b₂ m : M)
    (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source) (v : TangentSpace I m) :
    mfderiv I 𝓘(ℝ, E →L[ℝ] E) (coordGauge I b₁ b₂) m v =
      fderiv ℝ (fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm)) (extChartAt I b₂ m)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I b₂) m v) := by
  have hU : (chartAt H b₁).source ∩ (chartAt H b₂).source ∈ 𝓝 m :=
    ((chartAt H b₁).open_source.inter (chartAt H b₂).open_source).mem_nhds hm
  -- both maps are differentiable at `m`
  have hΩ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E) (coordGauge I b₁ b₂) m := by
    refine (ContMDiffAt.units_of_val (n := ∞) ?_).mdifferentiableAt (by simp)
    exact (contMDiffOn_coordChangeL (trivializationAt E (TangentSpace I) b₂)
      (trivializationAt E (TangentSpace I) b₁)).contMDiffAt (by rwa [Set.inter_comm] at hU)
  have hy : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I b₂) m := mdifferentiableAt_extChartAt hm.2
  -- read both manifold derivatives in the chart at `m`
  rw [hΩ.mfderiv_abuse, hy.mfderiv_abuse]
  simp only [I.range_eq_univ, fderivWithin_univ]
  -- `ψ` is `y` in the chart at `m`
  have hψp : writtenInExtChartAt I 𝓘(ℝ, E) m (extChartAt I b₂) (extChartAt I m m) =
      extChartAt I b₂ m := by
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_apply, id_eq, extChartAt_to_inv]
  have hψd : DifferentiableAt ℝ (writtenInExtChartAt I 𝓘(ℝ, E) m (extChartAt I b₂))
      (extChartAt I m m) := by
    have h := hy.differentiableWithinAt_writtenInExtChartAt
    rwa [I.range_eq_univ, differentiableWithinAt_univ] at h
  have hJd : DifferentiableAt ℝ (fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm))
      (writtenInExtChartAt I 𝓘(ℝ, E) m (extChartAt I b₂) (extChartAt I m m)) := by
    rw [hψp]
    exact ((contDiffAt_extChartAt_transition b₁ b₂ m hm).fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  -- near `extChartAt I m m`, the gauge map in the chart at `m` is `D(x ∘ y⁻¹) ∘ ψ`
  have heq : writtenInExtChartAt I 𝓘(ℝ, E →L[ℝ] E) m (coordGauge I b₁ b₂)
      =ᶠ[𝓝 (extChartAt I m m)]
      fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm) ∘
        writtenInExtChartAt I 𝓘(ℝ, E) m (extChartAt I b₂) := by
    filter_upwards [extChartAt_preimage_mem_nhds (I := I) hU] with z hz
    change ((coordGauge I b₁ b₂ ((extChartAt I m).symm z) : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) =
      fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm)
        (extChartAt I b₂ ((extChartAt I m).symm z))
    exact coe_coordGauge_of_boundaryless b₁ b₂ _ hz
  rw [heq.fderiv_eq, fderiv_comp _ hJd hψd, hψp]
  rfl

end SecondDerivative

section SchullerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The Christoffel transformation law in Schuller's form.**

With `x` the chart at `b₁`, `y` the chart at `b₂`, `Γ_x = σ_x^* ω` and `Γ_y = σ_y^* ω`:

  `Γ_y(v) = D(y ∘ x⁻¹) · Γ_x(v) · D(x ∘ y⁻¹) + D(y ∘ x⁻¹) · D²(x ∘ y⁻¹)(Dy v)`,

with the first derivatives taken at `x m` and `y m` respectively. In components, with
`v = ∂/∂y^ν`, this is
`Γ'ⁱⱼν = (∂yⁱ/∂xᵏ) Γᵏₗμ (∂xˡ/∂yʲ) (∂x^μ/∂y^ν) + (∂yⁱ/∂xᵏ) ∂²xᵏ/∂y^ν∂yʲ`. -/
theorem christoffel_transformation_chart
    [SmoothRightGAction ∞ (modelWithCornersSelf ℝ (E →L[ℝ] E))
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) (E →L[ℝ] E)ˣ ↑(FrameBundle I M)]
    (τ : ConnectionForm (G := (E →L[ℝ] E)ˣ) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (IB := I) (P := ↑(FrameBundle I M)))
    (b₁ b₂ m : M) (hm : m ∈ (chartAt H b₁).source ∩ (chartAt H b₂).source)
    (v : TangentSpace I m) :
    yangMillsField τ (coordFrame I b₂) m v =
      fderiv ℝ (extChartAt I b₂ ∘ (extChartAt I b₁).symm) (extChartAt I b₁ m) ∘L
        (yangMillsField τ (coordFrame I b₁) m v) ∘L
        fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm) (extChartAt I b₂ m) +
      fderiv ℝ (extChartAt I b₂ ∘ (extChartAt I b₁).symm) (extChartAt I b₁ m) ∘L
        fderiv ℝ (fderiv ℝ (extChartAt I b₁ ∘ (extChartAt I b₂).symm)) (extChartAt I b₂ m)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I b₂) m v) := by
  rw [christoffel_transformation τ b₁ b₂ m hm v, mfderiv_coordGauge b₁ b₂ m hm v,
    coe_coordGauge_inv b₁ b₂ m hm, coe_coordGauge_of_boundaryless b₂ b₁ m ⟨hm.2, hm.1⟩,
    coe_coordGauge_of_boundaryless b₁ b₂ m hm]

end SchullerForm

/-! ### Components

For `M` modelled on `ℝⁿ = Fin n → ℝ`, write `e_i` for the standard basis, `x` for the chart at
`b₁` and `y` for the chart at `b₂`. Then

* `coordVec b m μ` is `∂/∂x^μ` at `m` (for the chart at `b`);
* `jac b₁ b₂ m i j` is `∂xⁱ/∂yʲ` at `m`;
* `hess b₁ b₂ m k ν j` is `∂²xᵏ/∂y^ν∂yʲ` at `m`;
* `christoffel τ b m k l μ` is `Γᵏₗμ`, the `(k, l)` entry of `Γ(∂/∂x^μ)`. -/

section Components

variable {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The standard basis vector `e_i` of `ℝⁿ`, in the form `pi_eq_sum_univ` uses. -/
def stdVec (i : Fin n) : Fin n → ℝ := fun j => if i = j then 1 else 0

/-- A linear map on `ℝⁿ` in components: `(A w)ⁱ = Σₖ Aⁱₖ wᵏ`. -/
theorem clm_apply_eq_sum (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ) (i : Fin n) :
    A w i = ∑ k, A (stdVec k) i * w k := by
  conv_lhs => rw [pi_eq_sum_univ w]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stdVec]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The coordinate vector `∂/∂x^μ` at `m` for the chart at `b`. -/
def coordVec (b m : M) (μ : Fin n) : TangentSpace 𝓘(ℝ, Fin n → ℝ) m :=
  (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b).symmL ℝ m (stdVec μ)

/-- The Jacobian entry `∂xⁱ/∂yʲ` at `m`, with `x` the chart at `b₁` and `y` the chart at `b₂`. -/
def jac (b₁ b₂ m : M) (i j : Fin n) : ℝ :=
  fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm)
    (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m) (stdVec j) i

/-- The second derivative `∂²xᵏ/∂y^ν∂yʲ` at `m`. -/
def hess (b₁ b₂ m : M) (k ν j : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm))
    (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m) (stdVec ν) (stdVec j) k

/-- `Dy (∂/∂y^ν) = e_ν`. -/
theorem mfderiv_extChartAt_coordVec {b m : M} (hm : m ∈ (chartAt (Fin n → ℝ) b).source)
    (ν : Fin n) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) b) m
      (coordVec b m ν) = stdVec ν := by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hm]
  exact (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b).continuousLinearMapAt_symmL
    hm (stdVec ν)

/-- `∂/∂y^ν = Σ_μ (∂x^μ/∂y^ν) ∂/∂x^μ`. -/
theorem coordVec_eq_sum (b₁ b₂ m : M)
    (hm : m ∈ (chartAt (Fin n → ℝ) b₁).source ∩ (chartAt (Fin n → ℝ) b₂).source) (ν : Fin n) :
    coordVec b₂ m ν = ∑ μ, jac b₁ b₂ m μ ν • coordVec b₁ m μ := by
  have hΩ : (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b₂).coordChangeL ℝ
      (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b₁) m (stdVec ν) =
      fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m) (stdVec ν) :=
    congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => A (stdVec ν))
      (coe_coordGauge_of_boundaryless (I := 𝓘(ℝ, Fin n → ℝ)) b₁ b₂ m hm)
  unfold coordVec
  rw [← symmL_coordChangeL b₁ b₂ m hm, hΩ,
    pi_eq_sum_univ (fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘
      (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m) (stdVec ν)),
    map_sum]
  simp only [map_smul]
  rfl

variable
  [SmoothRightGAction ∞ (modelWithCornersSelf ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    ((𝓘(ℝ, Fin n → ℝ)).prod (modelWithCornersSelf ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))))
    ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))ˣ ↑(FrameBundle 𝓘(ℝ, Fin n → ℝ) M)]

/-- The local connection form `Γ = σ^* ω` of the coordinate frame of the chart at `b`, as a
matrix-valued 1-form. -/
def christoffelForm
    (τ : ConnectionForm (G := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))ˣ)
      (IG := modelWithCornersSelf ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
      (IB := 𝓘(ℝ, Fin n → ℝ)) (P := ↑(FrameBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (b m : M) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) m →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  @id (TangentSpace 𝓘(ℝ, Fin n → ℝ) m →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (yangMillsField τ (coordFrame 𝓘(ℝ, Fin n → ℝ) b) m)

/-- The Christoffel symbol `Γᵏₗμ` of the chart at `b`, at `m`. -/
def christoffel
    (τ : ConnectionForm (G := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))ˣ)
      (IG := modelWithCornersSelf ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
      (IB := 𝓘(ℝ, Fin n → ℝ)) (P := ↑(FrameBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (b m : M) (k l μ : Fin n) : ℝ :=
  christoffelForm τ b m (coordVec b m μ) (stdVec l) k

/-- **The Christoffel transformation law in components** (Schuller, Example 22.7).

With `x` the chart at `b₁` and `y` the chart at `b₂`,

  `Γ'ⁱⱼν = Σₖ Σₗ Σ_μ (∂yⁱ/∂xᵏ) Γᵏₗμ (∂xˡ/∂yʲ) (∂x^μ/∂y^ν) + Σₖ (∂yⁱ/∂xᵏ) ∂²xᵏ/∂y^ν∂yʲ`. -/
theorem christoffel_components
    (τ : ConnectionForm (G := ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))ˣ)
      (IG := modelWithCornersSelf ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
      (IB := 𝓘(ℝ, Fin n → ℝ)) (P := ↑(FrameBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (b₁ b₂ m : M)
    (hm : m ∈ (chartAt (Fin n → ℝ) b₁).source ∩ (chartAt (Fin n → ℝ) b₂).source)
    (i j ν : Fin n) :
    christoffel τ b₂ m i j ν =
      ∑ k, ∑ l, ∑ μ, jac b₂ b₁ m i k * christoffel τ b₁ m k l μ * jac b₁ b₂ m l j *
        jac b₁ b₂ m μ ν +
      ∑ k, jac b₂ b₁ m i k * hess b₁ b₂ m k ν j := by
  -- the operator form, evaluated at `v = ∂/∂y^ν`, with `Dy v = e_ν`
  have h : christoffelForm τ b₂ m (coordVec b₂ m ν) =
      fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁).symm)
          (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ m) ∘L
        (christoffelForm τ b₁ m (coordVec b₂ m ν)) ∘L
        fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm)
          (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m) +
      fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁).symm)
          (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ m) ∘L
        fderiv ℝ (fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) b₁ ∘
          (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂).symm)) (extChartAt 𝓘(ℝ, Fin n → ℝ) b₂ m)
          (stdVec ν) := by
    have h0 := christoffel_transformation_chart τ b₁ b₂ m hm (coordVec b₂ m ν)
    rw [mfderiv_extChartAt_coordVec hm.2 ν] at h0
    exact h0
  -- `Γ_x(∂/∂y^ν) = Σ_μ (∂x^μ/∂y^ν) Γ_x(∂/∂x^μ)`
  have hv : christoffelForm τ b₁ m (coordVec b₂ m ν) =
      ∑ μ, jac b₁ b₂ m μ ν • christoffelForm τ b₁ m (coordVec b₁ m μ) := by
    rw [coordVec_eq_sum b₁ b₂ m hm ν, map_sum]
    simp only [map_smul]
  rw [hv] at h
  unfold christoffel
  rw [h]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, Pi.add_apply]
  -- expand the outer `D(y ∘ x⁻¹)` in both terms
  rw [clm_apply_eq_sum _ _ i, clm_apply_eq_sum _ _ i]
  refine congrArg₂ (· + ·) ?_ rfl
  refine Finset.sum_congr rfl fun k _ => ?_
  -- expand `Γ_x(v)` applied to `D(x ∘ y⁻¹) e_j`, then the sum over `μ`
  rw [clm_apply_eq_sum _ _ k]
  simp only [_root_.sum_apply, _root_.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun μ _ => ?_
  unfold jac
  ring

end Components

