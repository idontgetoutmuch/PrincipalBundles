/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import PrincipalBundles.ExpLie
import PrincipalBundles.SmoothRightGAction
import PrincipalBundles.PrincipalBundle

/-!
# Fundamental vector fields on a principal G-bundle

For a principal `G`-bundle `P` and a Lie-algebra element `A ∈ 𝔤`, the fundamental
vector field `A#` at a point `p` is the velocity at `t = 0` of the curve
`t ↦ p <• expLie (t • A)`.

This file develops:
* `fundamentalVectorField`: the fundamental vector field,
* its identification with the derivative of the action `g ↦ p <• g`,
* linearity in `A`,
* that its flow is the action curve (`isMIntegralCurve_action_expLie`),
* smoothness,
* verticality (it lies in the kernel of `dproj`),
* and that `A# = 0 ⇒ A = 0` (freeness of the action).
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

instance [LieGroup IG ∞ G] : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

variable [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]

/-- The fundamental vector field `A#` associated to a Lie algebra element `A ∈ 𝔤` and a
point `p` in the total space of a principal `G`-bundle. -/
noncomputable def fundamentalVectorField
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    (A : GroupLieAlgebra IG G)
    (p : P) :
    TangentSpace (IB.prod IG) p :=
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
  mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
    (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A))
    (0 : ℝ) 1

/-- The adjoint representation `Ad_g : 𝔤 → 𝔤` of `g : G`. -/
noncomputable def Ad (g : G) : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h : G ↦ g * h * g⁻¹) 1

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_mem_vertical
    (A : GroupLieAlgebra IG G) (p : P) :
    mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p
      (fundamentalVectorField A p) = 0 := by
  unfold fundamentalVectorField
  have h118 : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG) (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2) (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2) (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    have h3 : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) := by
      have hconst : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
          (fun _ : ℝ ↦ p) := contMDiff_const
      have hprod : ContMDiff 𝓘(ℝ, ℝ) ((IB.prod IG).prod IG) (minSmoothness ℝ 2)
          (fun t : ℝ ↦ (p, expLie (IG := IG) (t • A))) :=
        hconst.prodMk h2
      have hsmul : ContMDiff ((IB.prod IG).prod IG) (IB.prod IG) (minSmoothness ℝ 2)
        (fun p : P × G => p.1 <• p.2) :=
        (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG) (G := G)
          (M := P)).of_le
            (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
      exact hsmul.comp hprod
    exact h3.mdifferentiableAt (by norm_num)
  have heval : (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = p := by
    simp [expLie_zero]
  have h121 : MDifferentiableAt (IB.prod IG) IB (fun p : P ↦ proj p)
    ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) := by
    rw [heval]
    exact (hPB.smooth_proj).mdifferentiableAt (by norm_num)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) IB ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 =
      (mfderiv (IB.prod IG) IB (fun p : P ↦ proj p)
        ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun (t : ℝ) ↦ p <• expLie (t • A)) 0) :=
    mfderiv_comp (0 : ℝ) h121 h118
  have hconst : ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) = fun _ ↦ proj p := by
    ext t
    exact hPB.respects_fibres p (expLie (t • A))
  have hzero : mfderiv% ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = 0 := by
    rw [hconst]
    exact mfderiv_const
  rw [heval] at hcomp
  rw [hzero] at hcomp
  have key : (mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p).comp
      (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0) = 0 := by
    rw [← hcomp]; exact rfl
  calc mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p
        (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0 1)
      = ((mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p).comp
          (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0)) 1 := rfl
    _ = 0 := by rw [key]; simp

lemma mfderiv_expLie
  (A : GroupLieAlgebra IG G) :
    mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 1 = A := by
  have hcurve : IsMIntegralCurve (fun t ↦ expLie (IG := IG) (t • A))
                                 (mulInvariantVectorField (I := IG) A) :=
    isMIntegralCurve_expLie_smul A
  have h0 := hcurve 0
  simp only [mulInvariantVectorField] at h0
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) IG
    (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight ((1 : ℝ →L[ℝ] ℝ))
      (((mfderiv% fun x ↦ expLie ((0 : ℝ) • A) * x) 1) A)) := h0
  rw [zero_smul, expLie_zero, one_mul] at h1
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (((mfderiv% fun x ↦ (1 : G) * x) 1) A)) := h1
  have hmul : mfderiv IG IG ((1 : G) * ·) 1 = ContinuousLinearMap.id ℝ (TangentSpace IG 1) := by
    have : ((1 : G) * ·) = id := by ext; simp
    rw [this, mfderiv_id]
  rw [hmul] at h2
  have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((ContinuousLinearMap.id ℝ (TangentSpace IG 1)) A)) := h2
  have h4 : (ContinuousLinearMap.id ℝ (TangentSpace IG 1)) A = A :=
    ContinuousLinearMap.id_apply A
  rw [h4] at h3
  have h5 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
             (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A) := h3
  have h6 : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A) 1 = A := by
    simp
  have h7 : mfderiv 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ) =
            ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A :=
    h5.mfderiv
  rw [h7]
  exact h6

section
open RightActions

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
     [IsManifold (IB.prod IG) ∞ P] in
lemma fundamentalVectorField_eq_mfderiv_action (p : P) :
    ∀ (A : GroupLieAlgebra IG G),
    fundamentalVectorField (IB := IB) (IG := IG) A p =
    mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1 A := by
  intro A
  have hg : MDifferentiableAt IG (IB.prod IG) (fun g : G ↦ p <• g)
      ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
    have h0 : ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) = 1 := by
      simp [zero_smul, expLie_zero]
    rw [h0]
    have := (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P))
    exact (this.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by norm_num)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2) (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2) (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact h2.mdifferentiableAt (by norm_num)
  have hh : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
        ((fun g : G ↦ p <• g) ∘ (fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0 =
      (mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g)
        ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0)).comp
        (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) :=
    mfderiv_comp 0 hg hf
  have hkey : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 1 =
      mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1 A := by
    have hmfderiv : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 =
        (mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1).comp
          (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
      have h1 : ((fun (g : G) ↦ p <• g) ∘ fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) =
               (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) :=
        Function.comp_def (fun g ↦ p <• g) fun t ↦ expLie (t • A)
      have h2 : (expLie ((0 : ℝ) • A)) = 1 := by simp [zero_smul, expLie_zero]
      rw [← h1, ← h2]
      exact hh
    simp only [hmfderiv]
    have h3 : ((mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0) 1 = A :=
      mfderiv_expLie (IG := IG) A
    exact congrArg _ h3
  unfold fundamentalVectorField
  exact hkey

noncomputable def fundamentalVectorFieldLinearMap (p : P) :
    GroupLieAlgebra IG G →ₗ[ℝ] TangentSpace (IB.prod IG) p where
  toFun A := fundamentalVectorField (IB := IB) (IG := IG) A p
  map_add' A B := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_add]
    exact rfl
  map_smul' r A := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_smul, RingHom.id_apply]
    exact rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (IB.prod IG) ∞ P] in
lemma isMIntegralCurve_action_expLie (p : P) (A : GroupLieAlgebra IG G) :
    IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
      (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) := by
  intro t
  have hflow : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A)) =
               (fun s : ℝ ↦ (p <• expLie (IG := IG) (t • A)) <• expLie (IG := IG) (s • A)) := by
    ext s
    have : expLie (IG := IG) ((t + s) • A) =
           expLie (IG := IG) (t • A) * expLie (IG := IG) (s • A) := expLie_add A t s
    rw [this, MulOpposite.op_mul, mul_smul]
  have hderiv : fundamentalVectorField (IB := IB) (IG := IG) A (p <• expLie (IG := IG) (t • A)) =
      mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun s ↦ p <• expLie (IG := IG) ((t + s) • A)) 0 1 := by
    rw [hflow]
    rfl
  simp only
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
      (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2)
        (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)).comp
      (contMDiff_const.prodMk h2)
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun t ↦ p <• expLie (IG := IG) (t • A)) t :=
    hsmooth.mdifferentiableAt (by norm_num)
  have hderiv2 := hmdiff.hasMFDerivAt
  -- Well-typed tangent-vector identity: fvf = (mfderiv% curve t) 1, via the shift reparametrization.
  have hshiftcomp : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A))
      = (fun u : ℝ ↦ p <• expLie (IG := IG) (u • A)) ∘ (fun s : ℝ ↦ t + s) := by
    ext s; simp only [Function.comp_apply]
  have hshift0 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ t + s) 0 :=
    (((hasDerivAt_id (0 : ℝ)).const_add t).hasFDerivAt.hasMFDerivAt).mdifferentiableAt
  have houter : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun u : ℝ ↦ p <• expLie (IG := IG) (u • A)) ((fun s : ℝ ↦ t + s) 0) := by
    rw [show (fun s : ℝ ↦ t + s) 0 = t by simp]; exact hmdiff
  have hcomp := mfderiv_comp (0 : ℝ) houter hshift0
  rw [← hshiftcomp] at hcomp
  have hval : fundamentalVectorField (IB := IB) (IG := IG) A (p <• expLie (IG := IG) (t • A))
      = (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
          (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) t) 1 := by
    rw [hderiv, hcomp]
    simp only [ContinuousLinearMap.comp_apply]
    have hkeyfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ t + s) 0 1 = 1 := by
      rw [mfderiv_eq_fderiv,
        show (fun s : ℝ ↦ t + s) = (fun s : ℝ ↦ t + id s) from rfl, fderiv_const_add]
      simp
      exact ContinuousLinearMap.id_apply 1
    rw [hkeyfd]
    rw [show (t : ℝ) + 0 = t from add_zero t]
  -- Close the main goal.
  refine hderiv2.congr_mfderiv ?_
  symm
  rw [hval]
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  exact rfl

-- set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] in
lemma contMDiff_fundamentalVectorField (A : GroupLieAlgebra IG G) :
    ContMDiff (IB.prod IG) (IB.prod IG).tangent (minSmoothness ℝ 1)
      (fun p : P ↦ (⟨p, fundamentalVectorField (IB := IB) (IG := IG) A p⟩ :
        TangentBundle (IB.prod IG) P)) := by
  haveI : IsManifold (IB.prod IG) 1 P := IsManifold.of_le (n := ∞) (by norm_num)
  have hsmooth : ContMDiff ((IB.prod IG).prod 𝓘(ℝ, ℝ)) (IB.prod IG) (minSmoothness ℝ 2)
      (fun (q : P × ℝ) ↦ q.1 <• expLie (IG := IG) (q.2 • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2)
        (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)).comp
      (contMDiff_fst.prodMk (h2.comp (contMDiff_snd (I := IB.prod IG) (J := 𝓘(ℝ, ℝ)))))
  intro q
  have hq := ContMDiffAt.mfderiv
    (N := P) (M := ℝ) (M' := P)
    (J := IB.prod IG) (I := 𝓘(ℝ, ℝ)) (I' := IB.prod IG)
    (m := minSmoothness ℝ 1) (n := minSmoothness ℝ 2) (x₀ := q)
    (fun p t ↦ p <• expLie (IG := IG) (t • A))
    (fun _ ↦ (0 : ℝ))
    (hsmooth.contMDiffAt)
    (contMDiffAt_const)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl (1 + 1))
  have hg0 : (fun x : P ↦ x <• expLie (IG := IG) ((0 : ℝ) • A)) = (fun x : P ↦ x) := by
    funext x
    have h1 : expLie (IG := IG) ((0 : ℝ) • A) = 1 := by
      have hz : ((0 : ℝ) • A) = (0 : GroupLieAlgebra IG G) := by
        show ((0 : ℝ) • (A : EG)) = (0 : EG)
        exact zero_smul ℝ (A : EG)
      rw [hz, expLie_zero]
    rw [h1]
    -- goal: x <• (1 : G) = x
    simp
  rw [hg0] at hq
  rw [contMDiffAt_section q]
  apply ContMDiffAt.congr_of_eventuallyEq (hq.clm_apply (contMDiffAt_const (c := (1 : ℝ))))
  filter_upwards [(chartAt (ModelProd HB HG) q).open_source.mem_nhds
    (mem_chart_source (ModelProd HB HG) q)] with x hx
  simp only [TangentBundle.trivializationAt_apply, fundamentalVectorField]
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply]
  have hrw := inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := IB.prod IG)
    (f := fun x ↦ (0 : ℝ)) (g := fun x ↦ x)
    (ϕ := fun x ↦ (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun (t : ℝ) ↦ x <• expLie (IG := IG) (t • A)) 0))
    (hx := ChartedSpace.mem_chart_source (0 : ℝ))
    (hy := hx)
  rw [hrw]
  simp only [tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, coe_achart,
    PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
    PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    Function.comp_apply, ContinuousLinearMap.coe_comp']
  simp only [modelWithCornersSelf_coe, OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.refl_source,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, OpenPartialHomeomorph.refl_apply,
    CompTriple.comp_eq,
    OpenPartialHomeomorph.refl_symm, modelWithCornersSelf_coe_symm, range_id, id_eq,
    fderivWithin_univ, fderiv_id, ContinuousLinearMap.coe_id']
  have hcomp : (↑(chartAt ℝ (0:ℝ)) ∘ ↑(chartAt ℝ (0:ℝ)).symm) = (id : ℝ → ℝ) := by
    funext y; simp [chartAt]
  rw [hcomp, fderiv_id]
  exact rfl

end

section
open RightActions
variable
  [T2Space P]
  [BoundarylessManifold (IB.prod IG) P]

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_zero_iff
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (p : P) (A : GroupLieAlgebra IG G) :
    fundamentalVectorField (IB := IB) (IG := IG) A p = 0 → A = 0 := by
  intro h
  have hconst : ∀ (t : ℝ), p <• expLie (IG := IG) (t • A) = p := by
    have hcurve : IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
        (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
      isMIntegralCurve_action_expLie p A
    have hconstcurve : IsMIntegralCurve (I := IB.prod IG) (fun _ : ℝ ↦ p)
        (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
      isMIntegralCurve_const h
    have heq : (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) = (fun _ ↦ p) := by
      apply isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
          (fun _ ↦ BoundarylessManifold.isInteriorPoint (I := IB.prod IG))
      · exact (contMDiff_fundamentalVectorField (IB := IB) (IG := IG) A).of_le (by norm_num)
      · exact hcurve
      · exact hconstcurve
      · simp [expLie_zero]
    exact fun t ↦ congr_fun heq t
  have hexp : ∀ (t : ℝ), expLie (IG := IG) (t • A) = 1 := by
    intro t
    have hfree := hPB.is_free p
    have hstab : MulOpposite.op (expLie (IG := IG) (t • A)) ∈
        MulAction.stabilizer (MulOpposite G) p := by
      simp [MulAction.mem_stabilizer_iff, hconst t]
    rw [hfree] at hstab
    simp only [Subgroup.mem_bot, MulOpposite.op_eq_one_iff] at hstab
    exact hstab
  have := mfderiv_expLie (IG := IG) A
  rw [show (fun t : ℝ ↦ expLie (IG := IG) (t • A)) = (fun _ ↦ (1 : G)) from
      funext hexp] at this
  simp [mfderiv_const] at this
  exact this.symm

end

/-- The Maurer-Cartan form on a Lie group `G`. -/
noncomputable def maurerCartan (g : G) : TangentSpace IG g →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h ↦ g⁻¹ * h) g

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
     [IsManifold (IB.prod IG) ∞ P] in
lemma mfderiv_action_at_g (p : P) (g : G) (w : TangentSpace IG g) :
    mfderiv IG (IB.prod IG) (p <• ·) g w =
      fundamentalVectorField (IB := IB) (IG := IG) (maurerCartan g w) (p <• g) := by
  rw [fundamentalVectorField_eq_mfderiv_action]
  have hdecomp : (fun g' : G ↦ p <• g') = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := by
    calc (fun g' : G ↦ p <• g') = (fun g' : G ↦ p <• (g * (g⁻¹ * g'))) := by
          simp [mul_inv_cancel_left]
      _ = (fun g' : G ↦ (p <• g) <• (g⁻¹ * g')) := by
          ext g'
          show p <• (g * (g⁻¹ * g')) = (p <• g) <• (g⁻¹ * g')
          rw [← mul_smul, MulOpposite.op_mul]
      _ = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := rfl
  have hLG : MDifferentiableAt IG IG (fun g' ↦ g⁻¹ * g') g :=
    (contMDiff_mul_left (a := g⁻¹) (n := ∞)).mdifferentiableAt (by norm_num)
  have hact : MDifferentiableAt IG (IB.prod IG) (fun h : G ↦ (p <• g) <• h) 1 :=
    ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).comp
      (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by norm_num)
  have hmC : mfderiv IG IG (fun g' ↦ g⁻¹ * g') g = maurerCartan g := rfl
  conv_lhs => rw [hdecomp]
  have hact' : MDifferentiableAt IG (IB.prod IG) (fun h : G ↦ (p <• g) <• h) (g⁻¹ * g) := by
    rw [inv_mul_cancel]
    exact hact
  rw [mfderiv_comp g hact' hLG, hmC]
  rw [inv_mul_cancel]
  haveI : Module ℝ (TangentSpace (IB.prod IG) (p <• g)) := inferInstance
  exact rfl

end
