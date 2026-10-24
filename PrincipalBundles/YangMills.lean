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
import PrincipalBundles.ConnectionForm

/-!
# Yang-Mills fields

Given a connection form `τ` on a principal `G`-bundle and a local section `σ`, the
Yang-Mills field (local gauge potential) is the pullback `σ^* ω`. This file proves its
transformation law under a change of gauge:

`yangMills_transformation`: `A₂ = Ad_{Ω⁻¹} A₁ + Ω^* (Maurer-Cartan)`.

## Main definitions

* `yangMillsField`: the local gauge potential `σ^* ω`

## Main results

* `mfderiv_smul_section`: Leibniz rule for the derivative of `x ↦ σ x <• Ω x`
* `mfderiv_localTriv_apply`: the derivative of the local trivialisation `(m, g) ↦ σ m <• g`
* `connectionForm_localTriv`: the connection form in a local trivialisation,
  `(h^* ω)(v, γ) = Ad_{g⁻¹}((σ^* ω)(v)) + Ξ_g(γ)` (Schuller, Theorem 22.2)
* `yangMills_transformation`: the gauge transformation law for Yang-Mills fields, as a corollary

## References

* Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Springer, 2017, §27
* Bleecker, *Gauge Theory and Variational Principles*, §1.2
* Schuller, *Lectures on the Geometric Anatomy of Theoretical Physics*, Lecture 22
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
  [ChartedSpace (ModelProd HB HG) P]
  [IsManifold (IB.prod IG) ∞ P]
  [MulAction (MulOpposite G) P]
  [SmoothRightGAction ∞ IG (IB.prod IG) G P]
  {proj : P → B}
  [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]

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
local instance : SeminormedAddCommGroup ((EB × EG) →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (SeminormedAddCommGroup ((EB × EG) →L[ℝ] EG))
local instance : NormedAddCommGroup ((EB × EG) →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedAddCommGroup ((EB × EG) →L[ℝ] EG))
local instance : NormedSpace ℝ ((EB × EG) →L[ℝ] GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedSpace ℝ ((EB × EG) →L[ℝ] EG))

/-- The Yang-Mills field associated to a local section `σ` of the principal bundle
    and a connection 1-form `ω` on `P`. -/
noncomputable def yangMillsField
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (P := P))
    (σ : B → P) :
    ∀ m : B, TangentSpace IB m →L[ℝ] GroupLieAlgebra IG G :=
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
    show NormedSpace ℝ EG from inferInstance
  fun m ↦ (τ.form.toFun (σ m)).comp (mfderiv IB (IB.prod IG) σ m)

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma mfderiv_smul_section
    (m : B)
    (σ : B → P) (Ω : B → G)
    (hσ : ContMDiffAt IB (IB.prod IG) ∞ σ m)
    (hΩ : ContMDiffAt IB IG ∞ Ω m)
    (v : TangentSpace IB m) :
    mfderiv IB (IB.prod IG) (fun x ↦ σ x <• Ω x) m v =
      mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ m) (mfderiv IB (IB.prod IG) σ m v) +
      mfderiv IG (IB.prod IG) (σ m <• ·) (Ω m) (mfderiv IB IG Ω m v) := by
  have hcomp : (fun x ↦ σ x <• Ω x) = (fun p : P × G ↦ p.1 <• p.2) ∘
    (fun x ↦ (σ x, Ω x)) := rfl
  rw [hcomp]
  have hpair : ContMDiffAt IB ((IB.prod IG).prod IG) ∞ (fun x ↦ (σ x, Ω x)) m :=
    hσ.prodMk hΩ
  have hsmul : MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
    (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m) :=
      (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
        (G := G) (M := P)).mdifferentiableAt (by norm_num)
  rw [mfderiv_comp m hsmul (hpair.mdifferentiableAt
       (by exact Ne.symm (not_eq_of_beq_eq_false rfl)))]
  have foo : ∀ w : TangentSpace ((IB.prod IG).prod IG) (σ m, Ω m),
      (mfderiv ((IB.prod IG).prod IG) (IB.prod IG)
        (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m)) w =
      (mfderiv (IB.prod IG) (IB.prod IG) (fun z ↦ z <• Ω m) (σ m)) w.1 +
      (mfderiv IG (IB.prod IG) (fun z ↦ σ m <• z) (Ω m)) w.2 :=
    fun w ↦ mfderiv_prod_eq_add_apply hsmul
  have hpair' : MDifferentiableAt IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m :=
    hpair.mdifferentiableAt (by norm_num)
  simp only [ContinuousLinearMap.comp_apply]
  rw [foo]
  congr 1
  · congr 1
    have hσ' : MDifferentiableAt IB (IB.prod IG) σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB (IB.prod IG) σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.fst_eq_iff.mpr rfl
  · congr 1
    have hσ' : MDifferentiableAt IB (IB.prod IG) σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB (IB.prod IG) σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.snd_eq_iff.mpr rfl

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
/-- The derivative of the local trivialisation `h(m, g) = σ m <• g` defined by a local section,
split into the part along the base and the part along the group. -/
lemma mfderiv_localTriv_apply (σ : B → P) (m : B) (g : G)
    (hσ : MDifferentiableAt IB (IB.prod IG) σ m)
    (v : TangentSpace IB m) (γ : TangentSpace IG g) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun p : B × G ↦ σ p.1 <• p.2) (m, g) (v, γ) =
      mfderiv (IB.prod IG) (IB.prod IG) (· <• g) (σ m) (mfderiv IB (IB.prod IG) σ m v) +
      mfderiv IG (IB.prod IG) (σ m <• ·) g γ := by
  have hsmul : ∀ q : P × G, MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
      (fun p : P × G ↦ p.1 <• p.2) q := fun q ↦
    (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).mdifferentiableAt (by norm_num)
  have hh : MDifferentiableAt (IB.prod IG) (IB.prod IG)
      (fun p : B × G ↦ σ p.1 <• p.2) (m, g) :=
    (hsmul (σ m, g)).comp (f := fun p : B × G ↦ (σ p.1, p.2)) (m, g)
      ((hσ.comp (f := Prod.fst) (m, g) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hR : MDifferentiableAt (IB.prod IG) (IB.prod IG) (· <• g) (σ m) :=
    (hsmul (σ m, g)).comp (f := fun z : P ↦ (z, g)) (σ m)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  rw [mfderiv_prod_eq_add_apply hh]
  dsimp only
  rw [show (fun z : B ↦ σ z <• g) = (· <• g) ∘ σ from rfl, mfderiv_comp m hR hσ]
  try rfl

/-- **Schuller, Theorem 22.2.** In the local trivialisation `h(m, g) = σ m <• g` defined by a
local section `σ`, the connection form is

  `(h^* ω)_{(m,g)}(v, γ) = Ad_{g⁻¹}((σ^* ω)(v)) + Ξ_g(γ)`,

with `Ξ` the Maurer–Cartan form. Schuller states this without proof; here it follows from the
splitting `mfderiv_localTriv_apply`, equivariance of `ω`, the identification of the derivative
of `g ↦ p <• g` as a fundamental vector field (`mfderiv_action_at_g`), and the reproducing
property of `ω`. -/
theorem connectionForm_localTriv
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (P := P))
    (σ : B → P) (m : B) (g : G) (hσ : MDifferentiableAt IB (IB.prod IG) σ m)
    (v : TangentSpace IB m) (γ : TangentSpace IG g) :
    τ.form.toFun (σ m <• g)
        (mfderiv (IB.prod IG) (IB.prod IG) (fun p : B × G ↦ σ p.1 <• p.2) (m, g) (v, γ)) =
      Ad g⁻¹ (yangMillsField (IB := IB) (IG := IG) τ σ m v) + maurerCartan g γ := by
  rw [mfderiv_localTriv_apply σ m g hσ v γ, map_add,
    τ.equivariant (σ m) g (mfderiv IB (IB.prod IG) σ m v),
    mfderiv_action_at_g (σ m) g γ, τ.reproduces_fundamental]
  try rfl

/-- The transformation law for Yang-Mills fields: the corollary of `connectionForm_localTriv`
obtained by pulling back along `m ↦ (m, Ω m)`, since `σ₂ = h ∘ (id, Ω)`. -/
theorem yangMills_transformation
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (P := P))
    (σ₁ σ₂ : B → P) (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (Ω : B → G) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : B) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace IB m) :
    yangMillsField (IB := IB) (IG := IG) τ σ₂ m v =
      Ad (Ω m)⁻¹ (yangMillsField (IB := IB) (IG := IG) τ σ₁ m v) +
      maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
  simp only [yangMillsField, ContinuousLinearMap.comp_apply]
  rw [← hΩ m hm]
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) := show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) := show NormedSpace ℝ EG from inferInstance
  have hmderiv_σ₂ : mfderiv IB (IB.prod IG) σ₂ m =
      mfderiv IB (IB.prod IG) (fun x ↦ σ₁ x <• Ω x) m :=
    have bar : U₁ ∩ U₂ ∈ nhds m := (hσ₁.1.inter hσ₂.1).mem_nhds hm
    Filter.EventuallyEq.mfderiv_eq (Filter.eventually_of_mem bar
      (fun x hx ↦ (hΩ x hx).symm))
  calc τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB (IB.prod IG) σ₂ m v)
      = τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB (IB.prod IG) (fun x ↦ σ₁ x <• Ω x) m v) := by
          congr 1; exact hmderiv_σ₂ ▸ rfl
    _ = τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ₁ m) (mfderiv IB (IB.prod IG) σ₁ m v) +
           mfderiv IG (IB.prod IG) (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v)) := by
          congr 1
          have hΩ_smooth : ContMDiffAt IB IG ∞ Ω m :=
            contMDiffAt_gaugeMap σ₁ σ₂ U₁ U₂ hσ₁ hσ₂ Ω hΩ m hm
          have foo : U₁ ∈ nhds m := hσ₁.1.mem_nhds hm.1
          exact mfderiv_smul_section m σ₁ Ω (hσ₁.2.1.contMDiffAt foo) hΩ_smooth v
    -- this is `h^* ω` at `(m, Ω m)` applied to `(v, dΩ v)`; apply Theorem 22.2
    _ = Ad (Ω m)⁻¹ (τ.form.toFun (σ₁ m) (mfderiv IB (IB.prod IG) σ₁ m v)) +
          maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
          have hσ₁' : MDifferentiableAt IB (IB.prod IG) σ₁ m :=
            (hσ₁.2.1.contMDiffAt (hσ₁.1.mem_nhds hm.1)).mdifferentiableAt (by norm_num)
          rw [← mfderiv_localTriv_apply σ₁ m (Ω m) hσ₁' v (mfderiv IB IG Ω m v)]
          exact connectionForm_localTriv τ σ₁ m (Ω m) hσ₁' v (mfderiv IB IG Ω m v)

end
