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
* `yangMills_transformation`: the gauge transformation law for Yang-Mills fields

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
  [hPB : IsPrincipalBundle IB G IG P IP proj]

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

/-- The Yang-Mills field associated to a local section `σ` of the principal bundle
    and a connection 1-form `ω` on `P`. -/
noncomputable def yangMillsField
    (τ : ConnectionForm (G := G) (IG := IG) (IP := IP) (P := P))
    (σ : B → P) :
    ∀ m : B, TangentSpace IB m →L[ℝ] GroupLieAlgebra IG G :=
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
    show NormedSpace ℝ EG from inferInstance
  fun m ↦ (τ.form.toFun (σ m)).comp (mfderiv IB IP σ m)

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma mfderiv_smul_section
    (m : B)
    (σ : B → P) (Ω : B → G)
    (hσ : ContMDiffAt IB IP ∞ σ m)
    (hΩ : ContMDiffAt IB IG ∞ Ω m)
    (v : TangentSpace IB m) :
    mfderiv IB IP (fun x ↦ σ x <• Ω x) m v =
      mfderiv IP IP (· <• Ω m) (σ m) (mfderiv IB IP σ m v) +
      mfderiv IG IP (σ m <• ·) (Ω m) (mfderiv IB IG Ω m v) := by
  have hcomp : (fun x ↦ σ x <• Ω x) = (fun p : P × G ↦ p.1 <• p.2) ∘
    (fun x ↦ (σ x, Ω x)) := rfl
  rw [hcomp]
  have hpair : ContMDiffAt IB (IP.prod IG) ∞ (fun x ↦ (σ x, Ω x)) m :=
    hσ.prodMk hΩ
  have hsmul : MDifferentiableAt (IP.prod IG) IP
    (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m) :=
      (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IP)
        (G := G) (M := P)).mdifferentiableAt (by norm_num)
  rw [mfderiv_comp m hsmul (hpair.mdifferentiableAt
       (by exact Ne.symm (not_eq_of_beq_eq_false rfl)))]
  have foo : ∀ w : TangentSpace (IP.prod IG) (σ m, Ω m),
      (mfderiv (IP.prod IG) IP
        (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m)) w =
      (mfderiv IP IP (fun z ↦ z <• Ω m) (σ m)) w.1 +
      (mfderiv IG IP (fun z ↦ σ m <• z) (Ω m)) w.2 :=
    fun w ↦ mfderiv_prod_eq_add_apply hsmul
  have hpair' : MDifferentiableAt IB (IP.prod IG) (fun x ↦ (σ x, Ω x)) m :=
    hpair.mdifferentiableAt (by norm_num)
  simp only [ContinuousLinearMap.comp_apply]
  rw [foo]
  congr 1
  · congr 1
    have hσ' : MDifferentiableAt IB IP σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB (IP.prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB IP σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.fst_eq_iff.mpr rfl
  · congr 1
    have hσ' : MDifferentiableAt IB IP σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB (IP.prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB IP σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.snd_eq_iff.mpr rfl

/-- The transformation law for Yang-Mills fields. -/
theorem yangMills_transformation
    (τ : ConnectionForm (G := G) (IG := IG) (IP := IP) (P := P))
    (σ₁ σ₂ : B → P) (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IP := IP) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IP := IP) (proj := proj) σ₂ U₂)
    (Ω : B → G) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : B) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace IB m) :
    yangMillsField (IB := IB) (IG := IG) τ σ₂ m v =
      Ad (Ω m)⁻¹ (yangMillsField (IB := IB) (IG := IG) τ σ₁ m v) +
      maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
  simp only [yangMillsField, ContinuousLinearMap.comp_apply]
  rw [← hΩ m hm]
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) := show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) := show NormedSpace ℝ EG from inferInstance
  have hmderiv_σ₂ : mfderiv IB IP σ₂ m =
      mfderiv IB IP (fun x ↦ σ₁ x <• Ω x) m :=
    have bar : U₁ ∩ U₂ ∈ nhds m := (hσ₁.1.inter hσ₂.1).mem_nhds hm
    Filter.EventuallyEq.mfderiv_eq (Filter.eventually_of_mem bar
      (fun x hx ↦ (hΩ x hx).symm))
  calc τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB IP σ₂ m v)
      = τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB IP (fun x ↦ σ₁ x <• Ω x) m v) := by
          congr 1; exact hmderiv_σ₂ ▸ rfl
    _ = τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv IP IP (· <• Ω m) (σ₁ m) (mfderiv IB IP σ₁ m v) +
           mfderiv IG IP (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v)) := by
          congr 1
          have hΩ_smooth : ContMDiffAt IB IG ∞ Ω m :=
            contMDiffAt_gaugeMap σ₁ σ₂ U₁ U₂ hσ₁ hσ₂ Ω hΩ m hm
          have foo : U₁ ∈ nhds m := hσ₁.1.mem_nhds hm.1
          exact mfderiv_smul_section m σ₁ Ω (hσ₁.2.1.contMDiffAt foo) hΩ_smooth v
    _ = τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv IP IP (· <• Ω m) (σ₁ m) (mfderiv IB IP σ₁ m v)) +
        τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv IG IP (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v)) := by
          exact map_add _ _ _
    _ = Ad (Ω m)⁻¹ (τ.form.toFun (σ₁ m) (mfderiv IB IP σ₁ m v)) +
          maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
          congr 1
          · exact τ.equivariant (σ₁ m) (Ω m) (mfderiv IB IP σ₁ m v)
          · have hfund : mfderiv IG IP (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v) =
                fundamentalVectorField (IP := IP) (IG := IG)
                  (maurerCartan (Ω m) (mfderiv IB IG Ω m v)) (σ₁ m <• Ω m) :=
              mfderiv_action_at_g (σ₁ m) (Ω m) (mfderiv IB IG Ω m v)
            rw [hfund, τ.reproduces_fundamental]

end
