/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import PrincipalBundles.FrameBundle
import TauCeti.Geometry.Manifold.FiberBundle.Principal

/-!
# The frame bundle as a principal bundle

Suppose you want to prove that the frame bundle is a principal bundle? One approach is to show
that it is an open subset of a vector bundle we already have, the bundle of linear maps from
\(\mathbb{R}^n\) to the tangent spaces of \(M\).

Let \(M\) be a manifold of dimension \(n\). A *frame* at a point \(x \in M\) is an ordered basis
\((e_1, \ldots, e_n)\) of the tangent space \(T_xM\).

A frame is the same thing as a linear isomorphism \(f : \mathbb{R}^n \to T_xM\). Let
\(\varepsilon_1, \ldots, \varepsilon_n\) be the standard basis of \(\mathbb{R}^n\). There are maps
in each direction.

*From isomorphisms to frames.* Send \(f\) to \((f(\varepsilon_1), \ldots, f(\varepsilon_n))\).
This is a basis of \(T_xM\), because an isomorphism takes a basis to a basis.

*From frames to isomorphisms.* Send \((e_1, \ldots, e_n)\) to the linear map

\[
f(a^1, \ldots, a^n) = \sum_{i=1}^n a^i e_i .
\]

It is injective because the \(e_i\) are linearly independent, and surjective because they span
\(T_xM\).

*The two maps are inverse to each other.*

- Start with a frame. The map \(f\) built from it has \(f(\varepsilon_i) = e_i\), so going back
  gives the same frame.
- Start with an isomorphism \(f\). The map built from its frame agrees with \(f\) on each
  \(\varepsilon_i\), so it equals \(f\), because a linear map is determined by its values on a
  basis.

From now on write \(E\) for \(\mathbb{R}^n\).

Write \(\mathrm{Hom}(E, TM)\) for the vector bundle whose fibre over \(x\) is the space of all
linear maps \(L(E, T_xM)\), invertible or not. The frame bundle is the subset

\[
F(M) = \{(x, f) \mid f : E \to T_xM \text{ is invertible}\} \subseteq \mathrm{Hom}(E, TM).
\]

\(F(M)\) is open.
-/

open Bundle Set Manifold
open scoped Manifold Topology ContDiff

noncomputable section

namespace FrameBundleExample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I ∞ M]

/-!
## The general approach

The total space is the open subset `FrameBundle I M` itself, with the manifold structure it has
as an open subset of the Hom bundle. Its local trivializations are the Hom-bundle
trivializations restricted to invertible frames (`frameBundleTriv`). Everything is in
`PrincipalBundles.FrameBundle`; here we only record the result.
-/

example :
    IsPrincipalBundle I (E →L[ℝ] E)ˣ 𝓘(ℝ, E →L[ℝ] E) ↥(FrameBundle I M)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) (frameBundleProj (I := I) (M := M)) :=
  FrameBundle.isPrincipalBundle

/-!
## The Tau Ceti approach

`TauCeti.PrincipalBundle G P` needs the total space as `Bundle.TotalSpace G P` for a family of
fibres `P : M → Type*`, with `FiberBundle G P`. Its smooth structure is then on the type copy
`TauCeti.ManifoldTotalSpace G P`, charted through the fibre, given
`TauCeti.ContMDiffFiberBundle`.

Each `sorry` below is a proof obligation that the general approach does not have.
-/

variable (I M) in
/-- The fibre over `x`: the invertible linear maps `E → T_xM`. -/
abbrev Fibre (x : M) : Type _ :=
  {f : Bundle.Trivial M E x →L[ℝ] TangentSpace I x // IsUnit f}

/-- `GL(E)` acts on each fibre on the right, by composition. -/
instance (x : M) : MulAction (MulOpposite (E →L[ℝ] E)ˣ) (Fibre I M x) where
  smul g f := ⟨f.1.comp (MulOpposite.unop g).val,
    (show IsUnit f.1 from f.2).mul (MulOpposite.unop g).isUnit⟩
  one_smul _ := Subtype.ext (ContinuousLinearMap.comp_id _)
  mul_smul _ _ _ := Subtype.ext (ContinuousLinearMap.comp_assoc _ _ _).symm

variable (I M) in
/-- The sigma-type total space and the open subset have the same points. -/
def frameEquiv : TotalSpace (E →L[ℝ] E)ˣ (Fibre I M) ≃ ↥(FrameBundle I M) where
  toFun z := ⟨⟨z.proj, z.2.1⟩, by exact z.2.2⟩
  invFun p := ⟨p.1.proj, ⟨p.1.2, show IsUnit p.1.2 from p.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology on the sigma-type total space, taken from the open subset. -/
instance : TopologicalSpace (TotalSpace (E →L[ℝ] E)ˣ (Fibre I M)) :=
  TopologicalSpace.induced (frameEquiv I M) inferInstance

variable (I M) in
/-- With that topology the identification is a homeomorphism. -/
def frameHomeomorph : TotalSpace (E →L[ℝ] E)ˣ (Fibre I M) ≃ₜ ↥(FrameBundle I M) :=
  (frameEquiv I M).toHomeomorphOfIsInducing ⟨rfl⟩

variable (I M) in
/-- Tau Ceti indexes trivializations by base points, not by frames, so we need a frame at each
base point: the inverse of the tangent-bundle trivialization at `b`. -/
def frameAt (b : M) : ↥(FrameBundle I M) :=
  ⟨⟨b, ((trivializationAt E (TangentSpace I) b).continuousLinearEquivAt ℝ b
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) b)).symm.toContinuousLinearMap⟩,
    sorry⟩

variable (I M) in
/-- The trivialization at `b`: `frameBundleTriv` moved across `frameHomeomorph`. -/
def trivAt (b : M) :
    Trivialization (E →L[ℝ] E)ˣ (TotalSpace.proj : TotalSpace (E →L[ℝ] E)ˣ (Fibre I M) → M) :=
  (frameBundleTriv (frameAt I M b)).compHomeomorph (frameHomeomorph I M)

instance : FiberBundle (E →L[ℝ] E)ˣ (Fibre I M) where
  totalSpaceMk_isInducing' _ := sorry
  trivializationAtlas' := Set.range (trivAt I M)
  trivializationAt' := trivAt I M
  mem_baseSet_trivializationAt' b := by
    exact FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] E)
      (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x) b
  trivialization_mem_atlas' b := ⟨b, rfl⟩

/-- Every trivialization in the atlas is equivariant. -/
instance : TauCeti.PrincipalBundle (E →L[ℝ] E)ˣ (Fibre I M) where
  isEquivariant_trivialization' _ _ := sorry

/-- The coordinate changes are smooth. -/
instance : TauCeti.ContMDiffFiberBundle ∞ (E →L[ℝ] E)ˣ (Fibre I M) I 𝓘(ℝ, E →L[ℝ] E) where
  contMDiffOn_coordChange _ _ _ _ := sorry

/-!
The two smooth structures, on `TauCeti.ManifoldTotalSpace` and on the open subset, are modelled
on the same space. To use results proved on one for the other we need the identification to be
a diffeomorphism.
-/

theorem contMDiff_toFrame :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] E)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : TauCeti.ManifoldTotalSpace (E →L[ℝ] E)ˣ (Fibre I M) =>
        frameHomeomorph I M
          ((TauCeti.ManifoldTotalSpace.homeomorph (E →L[ℝ] E)ˣ (Fibre I M)).symm x)) :=
  sorry

theorem contMDiff_ofFrame :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] E)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ↥(FrameBundle I M) =>
        TauCeti.ManifoldTotalSpace.homeomorph (E →L[ℝ] E)ˣ (Fibre I M)
          ((frameHomeomorph I M).symm p)) :=
  sorry

end FrameBundleExample
