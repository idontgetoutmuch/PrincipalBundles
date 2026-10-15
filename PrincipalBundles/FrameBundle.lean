/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import PrincipalBundles.Forms
import PrincipalBundles.YangMills
import PrincipalBundles.UnitsMFDeriv

/-!
# The Frame Bundle

The frame bundle of a smooth manifold `M` is the principal `GL(E)`-bundle whose fiber
over each point `x ∈ M` consists of all invertible linear maps `E → T_xM`. It is
constructed as an open subset of the Hom bundle `Hom(Trivial M E, TM)`.

## Main definitions

* `FrameBundle I M`: The frame bundle as an open subset of the Hom bundle
* `FrameBundle.isPrincipalBundle`: The frame bundle is a principal `GL(E)`-bundle

## References

* Tu, *Differential Geometry*, §13
-/

open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap RightActions FiberBundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

omit [CompleteSpace 𝕜] [CompleteSpace E] in
lemma isUnit_comp_iff_of_isUnit {D : E →L[𝕜] E} (hD : IsUnit D) (A : E →L[𝕜] E) :
    IsUnit (D.comp A) ↔ IsUnit A := by
  constructor <;> intro h;
  · obtain ⟨ u, hu ⟩ := h;
    obtain ⟨ v, hv ⟩ := hD;
    refine ⟨v⁻¹ * u, ?_⟩
    simp +decide only [Units.val_mul, hu]
    exact (Units.inv_mul_eq_iff_eq_mul v).mpr
      (congrFun (congrArg ContinuousLinearMap.comp (id (Eq.symm hv))) A)
  · exact hD.mul h

/-- In any monoid, composition with a unit on the left does not change invertibility.
Stated for continuous linear endomorphisms with no normed structure, so that it can be
instantiated at `TangentSpace I x` using only the canonical module instances — installing
local normed instances on the tangent space trips kernel-level aux-definition abstraction. -/
lemma isUnit_comp_iff_of_isUnit_weak {R M : Type*} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M]
    {D : M →L[R] M} (hD : IsUnit D) (A : M →L[R] M) :
    IsUnit (D.comp A) ↔ IsUnit A := by
  have h : D.comp A = (hD.unit : M →L[R] M) * A := by
    rw [IsUnit.unit_spec, ContinuousLinearMap.mul_def]
    -- if `mul_def` has drifted: `rfl` (mul on endomorphisms is defeq to comp)
  rw [h]
  constructor
  · intro hUA
    have hA : A = ((hD.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) *
        ((hD.unit : M →L[R] M) * A) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hA]
    exact (hD.unit⁻¹).isUnit.mul hUA
  · exact fun hA ↦ hD.unit.isUnit.mul hA

open Bundle FiberBundle

omit [CompleteSpace 𝕜] [CompleteSpace E] in
lemma isUnit_conj_iff (Φ : E ≃L[𝕜] E) (f : E →L[𝕜] E) :
    IsUnit (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ↔ IsUnit f := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨f, Φ.symm.toContinuousLinearMap ∘L u.inv ∘L Φ.toContinuousLinearMap, ?_, ?_⟩, rfl⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ∘L
               Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [Units.inv_eq_val_inv, ContinuousLinearMap.coe_comp',
                 ContinuousLinearEquiv.coe_coe, Function.comp_apply,
                 ContinuousLinearEquiv.apply_symm_apply]
      have : u.val (u.inv (Φ v)) = Φ v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ v)
        exact this
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv :=
        Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap)
               ∘L Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
                 Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      have : u.inv (u.val (Φ v)) = Φ v := by
        exact congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ v)
      rw [this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
  · rintro ⟨u, hu⟩
    refine ⟨⟨Φ.toContinuousLinearMap ∘L u ∘L Φ.symm.toContinuousLinearMap,
             Φ.toContinuousLinearMap ∘L u.inv ∘L Φ.symm.toContinuousLinearMap, ?_, ?_⟩,
            by simp [← hu]⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.val (u.inv (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.inv (u.val (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar]
      rw [this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v

omit [CompleteSpace 𝕜] [CompleteSpace E] [IsManifold I 1 M] in
/-- Frames at `x` compose as endomorphisms of the model space. Stated for every `x : M`, not
only for `p.proj` with `p` in a particular total space, so that instance search finds it at any
base point (e.g. `q.proj` in `FrameBundle`). -/
instance (x : M) : Monoid (Trivial M E x →L[𝕜] TangentSpace I x) :=
  inferInstanceAs (Monoid (E →L[𝕜] E))

omit [CompleteSpace 𝕜] [CompleteSpace E] [IsManifold I 1 M] in
/-- Coframes at `x` compose as endomorphisms of the model space; see the instance above. -/
instance (x : M) : Monoid (TangentSpace I x →L[𝕜] E) :=
  inferInstanceAs (Monoid (E →L[𝕜] E))

/-- The frame bundle of a smooth manifold `M` is the open subset of the
    Hom bundle `Hom(TM, TM)` consisting of invertible elements. -/
def FrameBundle (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompleteSpace E] : TopologicalSpace.Opens
    (TotalSpace (E →L[𝕜] E) (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)) where
  carrier := {p | IsUnit p.2}
  is_open' := by
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    set e := trivializationAt (E →L[𝕜] E)
      (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.proj
    have hpe : p ∈ e.source := mem_trivializationAt_proj_source
    refine ⟨e.source ∩ e ⁻¹' (e.baseSet ×ˢ {f : E →L[𝕜] E | IsUnit f}),
            fun q ⟨hqs, hq⟩ => ?_,
            e.continuousOn.isOpen_inter_preimage e.open_source (e.open_baseSet.prod Units.isOpen),
            ⟨hpe, ?_⟩⟩
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq] at hq
      have hb := e.mem_source.mp hqs
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)] at hq
      have hb_triv : q.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : q.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan] at hq
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) q.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id] at hq
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      exact (isUnit_comp_iff_of_isUnit_weak htan_unit q.2).mp hq.2
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
      have hb := e.mem_source.mp hpe
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)]
      have hb_triv : p.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : p.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      refine ⟨hb, ?_⟩
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan]
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) p.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id]
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      exact (isUnit_comp_iff_of_isUnit_weak htan_unit p.2).mpr hp

instance [IsManifold I ∞ M] [CompleteSpace E] :
    IsManifold (I.prod 𝓘(𝕜, E →L[𝕜] E)) ∞ ↥(FrameBundle I M) := inferInstance

instance [CompleteSpace E] : LieGroup (modelWithCornersSelf 𝕜 (E →L[𝕜] E)) ∞
    (Units (E →L[𝕜] E)) := inferInstance

noncomputable def frameBundleProj [IsManifold I ∞ M] :
    ↥(FrameBundle I M) → M :=
  fun p => p.1.proj

noncomputable instance frameBundleMulAction [IsManifold I ∞ M] :
    MulAction (MulOpposite (Units (E →L[𝕜] E))) ↥(FrameBundle I M) where
  smul g p :=
    ⟨⟨p.1.proj, p.1.snd.comp (MulOpposite.unop g).val⟩,
     (show IsUnit p.1.snd from p.2).mul (MulOpposite.unop g).isUnit⟩
  one_smul := fun p => by
    apply Subtype.ext; apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (ContinuousLinearMap.comp_id _)
  mul_smul := fun g h p => by
    apply Subtype.ext; apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (ContinuousLinearMap.comp_assoc _ _ _).symm

omit [CompleteSpace 𝕜] in
omit [IsManifold I 1 M] in
lemma frameBundleAction_respects_fibres [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) (g : Units (E →L[𝕜] E)) :
    frameBundleProj (p <• g) = frameBundleProj p := by
  rfl

omit [CompleteSpace 𝕜] in
lemma frameBundleAction_free [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) :
    MulAction.stabilizer (MulOpposite (Units (E →L[𝕜] E))) p = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  -- `g • p` has the same base point as `p` and frame `p.1.2 ∘L g.unop`.
  have h1 : p.1.2 ∘L (MulOpposite.unop g).val = p.1.2 :=
    eq_of_heq (congr_arg_heq (fun q : ↥(FrameBundle I M) => q.1.2) hg)
  -- A frame is invertible, hence injective, so it cancels on the left.
  obtain ⟨u, hu⟩ := p.2
  have hinj : Function.Injective p.1.2 := by
    have key : ∀ w, u.inv (p.1.2 w) = w := fun w => by
      rw [← hu]
      exact congrArg (fun F => F w) u.inv_val
    intro a b hab
    exact (key a).symm.trans ((congrArg u.inv hab).trans (key b))
  have h2 : (MulOpposite.unop g).val = (1 : E →L[𝕜] E) :=
    ContinuousLinearMap.ext fun v => hinj (congrArg (fun F => F v) h1)
  rw [Subgroup.mem_bot]
  exact MulOpposite.unop_injective (Units.ext (h2.trans Units.val_one.symm))

section UnitsTransfer

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  {R : Type*} [NormedRing R] [NormedAlgebra 𝕜' R] [CompleteSpace R]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜' EN]
  {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜' EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- A map into the units of a complete normed algebra is `C^n` as soon as its composite
with `Units.val` is: the single chart on `Rˣ` is `Units.val` itself. -/
lemma ContMDiffAt.units_of_val {f : N → Rˣ} {x : N} {n : WithTop ℕ∞}
    (h : ContMDiffAt IN 𝓘(𝕜', R) n (fun y ↦ (f y : R)) x) :
    ContMDiffAt IN 𝓘(𝕜', R) n f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨Units.isOpenEmbedding_val.isInducing.continuousAt_iff.mpr h.continuousAt, ?_⟩
  -- the goal is `ContMDiffAt _ _ n (extChartAt 𝓘(𝕜', R) (f x) ∘ f) x`; the chart of the
  -- singleton charted space on `Rˣ` is `Units.val` and the model is the identity, so the
  -- composite is definitionally `fun y ↦ (f y : R)`.
  -- If the `rfl` below fails, replace it with
  --   `simp [extChartAt, OpenPartialHomeomorph.extend]` (or find the unfolding via `simp?`).
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ rfl)

end UnitsTransfer

section UnitsRestrict

/-! ### Restricting a trivialisation to its invertible part

Let `e` be a local trivialisation of a bundle whose fibre is a complete normed ring `R`, and let
`P` be a set of points of the total space which, over the base set of `e`, consists exactly of
the points whose fibre coordinate is invertible. Then `e` restricts to a local trivialisation of
`P` with fibre `Rˣ`. For the frame bundle, `R` is `E →L[ℝ] E` and `P` is the set of invertible
frames, so this gives the local trivialisations of the frame bundle directly from those of the
Hom bundle. -/

variable {B Z : Type*} [TopologicalSpace B] [TopologicalSpace Z] {proj : Z → B}
  {R : Type*} [NormedRing R] [CompleteSpace R]

open Classical in
/-- The unit with value `a` when `a` is invertible, and `1` otherwise. -/
noncomputable def unitCoord (a : R) : Rˣ := if h : IsUnit a then h.unit else 1

lemma val_unitCoord {a : R} (h : IsUnit a) : (unitCoord a : R) = a := by
  unfold unitCoord
  rw [dif_pos h]
  exact h.unit_spec

open Classical in
/-- The restriction of `e` to `P`, with fibre `Rˣ`. The point `p₀` is a junk value off the
target. -/
noncomputable def Bundle.Trivialization.restrictUnits (e : Trivialization R proj) (P : Set Z)
    (hP : ∀ z ∈ e.source, z ∈ P ↔ IsUnit (e z).2) (p₀ : P) :
    Trivialization Rˣ (fun z : P => proj z) where
  toFun z := (proj z, unitCoord (e z).2)
  invFun x :=
    if h : x.1 ∈ e.baseSet then
      ⟨e.toOpenPartialHomeomorph.symm (x.1, (x.2 : R)),
        (hP _ (e.map_target (e.mem_target (x := (x.1, (x.2 : R))) |>.mpr h))).mpr
          (by rw [e.apply_symm_apply' h]; exact x.2.isUnit)⟩
    else p₀
  source := Subtype.val ⁻¹' e.source
  target := e.baseSet ×ˢ Set.univ
  map_source' z hz := Set.mk_mem_prod ((e.mem_source (x := z.1)).mp hz) (Set.mem_univ _)
  map_target' x hx := by
    have h : x.1 ∈ e.baseSet := hx.1
    simp only [Set.mem_preimage, dif_pos h]
    exact e.map_target (e.mem_target (x := (x.1, (x.2 : R))) |>.mpr h)
  left_inv' z hz := by
    have hb : proj z ∈ e.baseSet := (e.mem_source (x := z.1)).mp hz
    apply Subtype.ext
    simp only [dif_pos hb]
    rw [val_unitCoord ((hP z.1 hz).mp z.2), e.mk_proj_snd (x := z.1) hz]
    exact e.toOpenPartialHomeomorph.left_inv (x := z.1) hz
  right_inv' x hx := by
    obtain ⟨b, g⟩ := x
    have h : b ∈ e.baseSet := hx.1
    simp only [dif_pos h]
    rw [e.proj_symm_apply' h, e.apply_symm_apply' h]
    exact Prod.ext rfl (Units.ext (val_unitCoord g.isUnit))
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    have hsrc : Set.MapsTo (Subtype.val : P → Z) (Subtype.val ⁻¹' e.source) e.source :=
      fun _ hz => hz
    have he : ContinuousOn (fun z : P => e z) (Subtype.val ⁻¹' e.source) :=
      e.toOpenPartialHomeomorph.continuousOn.comp continuous_subtype_val.continuousOn hsrc
    refine ContinuousOn.prodMk
      (e.continuousOn_proj.comp continuous_subtype_val.continuousOn hsrc) ?_
    rw [Units.isOpenEmbedding_val.isInducing.continuousOn_iff]
    exact (continuous_snd.comp_continuousOn he).congr fun z hz =>
      val_unitCoord ((hP z.1 hz).mp z.2)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hf : ContinuousOn (fun x : B × Rˣ => e.toOpenPartialHomeomorph.symm (x.1, (x.2 : R)))
        (e.baseSet ×ˢ Set.univ) :=
      e.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)).continuousOn
        (fun x hx => e.mem_target.mpr hx.1)
    refine hf.congr fun x hx => ?_
    simp only [Function.comp_apply, dif_pos hx.1]
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by
    ext z
    exact e.mem_source
  target_eq := rfl
  proj_toFun _ _ := rfl

lemma Bundle.Trivialization.restrictUnits_baseSet (e : Trivialization R proj) (P : Set Z)
    (hP : ∀ z ∈ e.source, z ∈ P ↔ IsUnit (e z).2) (p₀ : P) :
    (e.restrictUnits P hP p₀).baseSet = e.baseSet :=
  rfl

/-- On its source, the fibre coordinate of the restriction is the fibre coordinate of `e`. -/
lemma Bundle.Trivialization.coe_snd_restrictUnits (e : Trivialization R proj) (P : Set Z)
    (hP : ∀ z ∈ e.source, z ∈ P ↔ IsUnit (e z).2) (p₀ : P) {z : P} (hz : (z : Z) ∈ e.source) :
    ((e.restrictUnits P hP p₀ z).2 : R) = (e z).2 :=
  val_unitCoord ((hP z.1 hz).mp z.2)

end UnitsRestrict

section FrameBundleRL  -- restricted to ℝ for IsPrincipalBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- The Hom-bundle trivialisation over the chart at `b` sends a frame `z` at `x` to
`τₓ ∘ z`, where `τₓ` is the tangent-bundle trivialisation at `x`. -/
lemma hom_trivializationAt_snd_eq (b : M)
    (z : TotalSpace (E →L[ℝ] E) (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x))
    (hb : z.proj ∈ (trivializationAt E (TangentSpace I) b).baseSet) :
    (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) b z).2 =
      ((trivializationAt E (TangentSpace I) b).continuousLinearEquivAt ℝ z.proj hb
        ).toContinuousLinearMap.comp z.2 := by
  have hb_triv : z.proj ∈ (trivializationAt E (Bundle.Trivial M E) b).baseSet := by simp
  rw [hom_trivializationAt_apply (σ := RingHom.id ℝ),
    ContinuousLinearMap.inCoordinates_eq hb_triv hb]
  have htriv_symm : (Trivialization.continuousLinearEquivAt ℝ
      (trivializationAt E (Bundle.Trivial M E) b) z.proj hb_triv).symm =
      ContinuousLinearEquiv.refl ℝ E := by
    simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
      ContinuousLinearEquiv.refl_symm]
  simp only [htriv_symm, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id]
  try rfl

/-- On the source of a Hom-bundle trivialisation, a frame is invertible exactly when its
coordinate is. -/
lemma isUnit_iff_hom_trivializationAt (b : M)
    (z : TotalSpace (E →L[ℝ] E) (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x))
    (hz : z ∈ (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) b).source) :
    IsUnit z.2 ↔ IsUnit (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) b z).2 := by
  have hb : z.proj ∈ (trivializationAt E (TangentSpace I) b).baseSet := by
    have h := (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) b).mem_source.mp hz
    rw [hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id ℝ)
      (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) b] at h
    exact h.2
  rw [hom_trivializationAt_snd_eq b z hb]
  -- `τ` is the tangent trivialisation at `z.proj`; read everything in `E →L[ℝ] E`
  let τ := (trivializationAt E (TangentSpace I) b).continuousLinearEquivAt ℝ z.proj hb
  let T : E →L[ℝ] E := @id (E →L[ℝ] E) τ.toContinuousLinearMap
  let T' : E →L[ℝ] E := @id (E →L[ℝ] E) τ.symm.toContinuousLinearMap
  have hT : IsUnit T :=
    ⟨⟨T, T', by ext x; exact τ.apply_symm_apply x, by ext x; exact τ.symm_apply_apply x⟩, rfl⟩
  exact (isUnit_comp_iff_of_isUnit hT (@id (E →L[ℝ] E) z.2)).symm

/-- The local trivialisation of the frame bundle at `p`: the Hom-bundle trivialisation over the
chart at `p.proj`, restricted to invertible frames. -/
noncomputable def frameBundleTriv [IsManifold I ∞ M] (p : ↥(FrameBundle I M)) :
    Trivialization (E →L[ℝ] E)ˣ (frameBundleProj (I := I) (M := M)) :=
  (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).restrictUnits
    (FrameBundle I M : Set _)
    (fun z hz => isUnit_iff_hom_trivializationAt p.1.proj z hz) p

/-- On its source, the fibre coordinate of `frameBundleTriv p` is the Hom-bundle coordinate. -/
lemma coe_snd_frameBundleTriv [IsManifold I ∞ M] (p : ↥(FrameBundle I M)) {r : ↥(FrameBundle I M)}
    (hr : r.1 ∈ (trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).source) :
    ((frameBundleTriv p r).2 : E →L[ℝ] E) =
      (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj r.1).2 :=
  Trivialization.coe_snd_restrictUnits _ _ _ _ hr

noncomputable instance FrameBundle.isPrincipalBundle [IsManifold I ∞ M] :
    IsPrincipalBundle
      I
      (Units (E →L[ℝ] E))
      (modelWithCornersSelf ℝ (E →L[ℝ] E))
      ↥(FrameBundle I M)
      (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (frameBundleProj (I := I) (M := M)) where
  is_free := frameBundleAction_free
  respects_fibres := frameBundleAction_respects_fibres
  smooth_proj := by
    apply ContMDiff.comp (I' := I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
    · exact contMDiff_proj (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x)
    · exact contMDiff_subtype_val
  localTriv := frameBundleTriv
  mem_baseSet_localTriv := fun p =>
    mem_baseSet_trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj
  equivariant_localTriv := fun p q hq g => by
    -- `q • g` has the same base point as `q`, and frame `q.2 ∘ g`.
    have hq₁ : q.1 ∈ (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).source := hq
    have hqg : (q <• g).1 ∈ (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).source :=
      (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).mem_source.mpr
        ((trivializationAt (E →L[ℝ] E)
          (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).mem_source.mp hq₁)
    have hb : q.1.proj ∈ (trivializationAt E (TangentSpace I) p.1.proj).baseSet := by
      have h := (trivializationAt (E →L[ℝ] E)
        (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj).mem_source.mp hq₁
      rw [hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id ℝ)
        (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.1.proj] at h
      exact h.2
    refine Prod.ext rfl (Units.ext ?_)
    -- `τ ∘ (q.2 ∘ g) = (τ ∘ q.2) ∘ g`, with `τ` the tangent trivialisation at `q.proj`
    rw [Units.val_mul, coe_snd_frameBundleTriv p hqg, coe_snd_frameBundleTriv p hq₁,
      hom_trivializationAt_snd_eq p.1.proj (q <• g).1 hb,
      hom_trivializationAt_snd_eq p.1.proj q.1 hb]
    rfl
  smooth_localTriv := fun p => by
    intro q hq
    apply ContMDiffAt.contMDiffWithinAt
    set e' := trivializationAt (E →L[ℝ] E)
      (fun x => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) p.1.proj with he'def
    have hq₁ : q.1 ∈ e'.source := hq
    -- the Hom-bundle trivialization is smooth (ContMDiffVectorBundle on the Hom bundle)
    have he'_smooth : ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] E)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (⇑e') q.1 :=
      e'.contMDiffOn.contMDiffAt (e'.open_source.mem_nhds hq₁)
    have hval : ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun r : ↥(FrameBundle I M) ↦ (e' r.1).2) q :=
      contMDiff_snd.contMDiffAt.comp q
        (he'_smooth.comp q contMDiff_subtype_val.contMDiffAt)
    -- on the source, the fibre coordinate of `frameBundleTriv p` is that of `e'`
    have hopen : IsOpen ((frameBundleTriv p).source) := (frameBundleTriv p).open_source
    have hcongr : ∀ r : ↥(FrameBundle I M), r ∈ (frameBundleTriv p).source →
        ((frameBundleTriv p r).2 : E →L[ℝ] E) = (e' r.1).2 := fun r hr ↦
      coe_snd_frameBundleTriv p hr
    have hsnd : ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun r : ↥(FrameBundle I M) ↦ (frameBundleTriv p r).2) q := by
      apply ContMDiffAt.units_of_val
      exact hval.congr_of_eventuallyEq
        (Filter.eventually_of_mem (hopen.mem_nhds hq) hcongr)
    have hfst : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] E)) I ∞
        (fun r : ↥(FrameBundle I M) ↦ r.1.proj) := by
      apply ContMDiff.comp (I' := I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
      · exact contMDiff_proj (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x)
      · exact contMDiff_subtype_val
    -- `frameBundleTriv p r` is `(r.proj, (frameBundleTriv p r).2)` by definition
    exact hfst.contMDiffAt.prodMk hsnd

end FrameBundleRL

section FrameBundleYangMills

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- `maurerCartan` for `(E →L[ℝ] E)ˣ` is left-multiplication by `g⁻¹`. -/
lemma maurerCartan_units_eq
    (g : (E →L[ℝ] E)ˣ) (v : E →L[ℝ] E) :
    maurerCartan (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) g v =
      (g⁻¹ : (E →L[ℝ] E)ˣ).val ∘L v := by
  simp only [maurerCartan]
  exact mfderiv_units_mulLeft g⁻¹ g v

/-- `Ad_{g⁻¹}` for `(E →L[ℝ] E)ˣ` is conjugation. -/
lemma Ad_units_eq
    (g : (E →L[ℝ] E)ˣ) (A : E →L[ℝ] E) :
    Ad (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) g⁻¹ A =
      (g⁻¹ : (E →L[ℝ] E)ˣ).val ∘L A ∘L g.val := by
  simp only [Ad]
  refine (mfderiv_units_mul_mul g⁻¹ g⁻¹⁻¹ A).trans ?_
  simp only [inv_inv]
  rw [mul_assoc]
  rfl

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Yang-Mills connection transformation law for the frame bundle, in coordinates.
This is the coordinate form of the abstract `yangMills_transformation`: for the frame bundle
the group is `(E →L[ℝ] E)ˣ`, the adjoint action `Ad_{g⁻¹}` is conjugation and the Maurer-Cartan
form `maurerCartan g` is left multiplication by `g⁻¹`. -/
theorem frameBundleYangMills_transformation
    [SmoothRightGAction ∞ (modelWithCornersSelf ℝ (E →L[ℝ] E))
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) (E →L[ℝ] E)ˣ ↑(FrameBundle I M)]
    (τ : ConnectionForm (G := (E →L[ℝ] E)ˣ) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (IB := I) (P := ↑(FrameBundle I M)))
    (σ₁ σ₂ : M → ↑(FrameBundle I M)) (U₁ U₂ : Set M)
    (hσ₁ : IsLocalSection (IB := I) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (proj := frameBundleProj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := I) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (proj := frameBundleProj) σ₂ U₂)
    (Ω : M → (E →L[ℝ] E)ˣ) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : M) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace I m) :
    yangMillsField τ σ₂ m v =
      (Ω m)⁻¹.val ∘L (yangMillsField τ σ₁ m v) ∘L (Ω m).val +
      (Ω m)⁻¹.val ∘L (mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] E)) Ω m v) := by
  rw [yangMills_transformation τ σ₁ σ₂ U₁ U₂ hσ₁ hσ₂ Ω hΩ m hm v,
    show (Ad (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) (Ω m)⁻¹) (yangMillsField τ σ₁ m v) = _
      from Ad_units_eq (Ω m) _,
    show (maurerCartan (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) (Ω m))
        (mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] E)) Ω m v) = _
      from maurerCartan_units_eq (Ω m) _]
  rfl
end FrameBundleYangMills
