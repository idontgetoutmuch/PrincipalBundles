/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import PrincipalBundles.ExpLie
import PrincipalBundles.SmoothRightGAction
import PrincipalBundles.PrincipalBundle
import PrincipalBundles.FundamentalVectorField

/-!
# Connection forms on a principal G-bundle

A connection on a principal `G`-bundle `P` is a Lie-algebra-valued 1-form `ω` on the
total space satisfying two axioms:

* `reproduces_fundamental`: `ω` sends the fundamental vector field `A#` back to `A`,
* `equivariant`: `R_g^* ω = Ad_{g⁻¹} ∘ ω`.

## Main definitions

* `LieAlgebraValuedOneForm`: a smooth `𝔤`-valued 1-form on `P`
* `ConnectionForm`: such a form satisfying the two connection axioms

## References

* Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Springer, 2017, §27
* Bleecker, *Gauge Theory and Variational Principles*, §1.2
-/

open Bundle RightActions
open Set Bundle ContDiff Manifold Trivialization

noncomputable section

variable
  {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {G : Type*} [TopologicalSpace G] [T2Space G]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [Group G]
  [LieGroup IG ∞ G]
  [BoundarylessManifold IG G]
  {P : Type*}
  [TopologicalSpace P]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP}
  [ChartedSpace HP P]
  [IsManifold IP ∞ P]
  [MulAction (MulOpposite G) P]
  [SmoothRightGAction ∞ IG IP G P]
  {proj : P → B}

variable [hPB : IsPrincipalBundle IB G IG P IP proj]

attribute [-instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle
  Bundle.ContinuousLinearMap.vectorBundle in
def LieAlgebraValuedOneForm :=
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) := inferInstanceAs (NormedAddCommGroup EG)
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) := inferInstanceAs (NormedSpace ℝ EG)
  letI : NormedAddCommGroup (EP →L[ℝ] GroupLieAlgebra IG G) :=
    inferInstanceAs (NormedAddCommGroup (EP →L[ℝ] EG))
  letI : NormedSpace ℝ (EP →L[ℝ] GroupLieAlgebra IG G) :=
    inferInstanceAs (NormedSpace ℝ (EP →L[ℝ] EG))
  Cₛ^∞⟮IP; EP →L[ℝ] GroupLieAlgebra IG G,
    Bundle.Trivial P (EP →L[ℝ] GroupLieAlgebra IG G)⟯

section
set_option backward.isDefEq.respectTransparency false
attribute [-instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle
  Bundle.ContinuousLinearMap.vectorBundle

local instance : SeminormedAddCommGroup (GroupLieAlgebra IG G) :=
  inferInstanceAs (SeminormedAddCommGroup EG)
local instance : NormedAddCommGroup (GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedAddCommGroup EG)
local instance : NormedSpace ℝ (GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedSpace ℝ EG)
local instance : SeminormedAddCommGroup (EP →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (SeminormedAddCommGroup (EP →L[ℝ] EG))
local instance : NormedAddCommGroup (EP →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedAddCommGroup (EP →L[ℝ] EG))
local instance : NormedSpace ℝ (EP →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedSpace ℝ (EP →L[ℝ] EG))

structure ConnectionForm where
  form : LieAlgebraValuedOneForm (G := G) (IG := IG) (IP := IP) (P := P)
  reproduces_fundamental :
    ∀ (p : P) (A : GroupLieAlgebra IG G),
    form.toFun p (fundamentalVectorField (IP := IP) (IG := IG) A p) = A
  equivariant :
    ∀ (p : P) (g : G) (v : TangentSpace IP p),
    form.toFun (p <• g) (mfderiv IP IP (· <• g) p v) =
      Ad g⁻¹ (form.toFun p v)

end
