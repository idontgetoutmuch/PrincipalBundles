/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import PrincipalBundles.SmoothRightGAction

/-!
# Principal Bundles (Abstract formulation)

A smooth principal G-bundle over a manifold B is a smooth manifold P equipped with:
1. A smooth right G-action on P
2. A smooth projection `proj : P → B` that is G-invariant
3. G-equivariant local trivializations

This file develops the abstract theory for an arbitrary total space `P`.

Transitivity of the G-action on fibers is a consequence of equivariance and is proved
as a separate proposition. Gauge transition maps between local sections are shown to be
smooth.

## Main definitions

* `IsPrincipalBundle`: A smooth principal G-bundle with an arbitrary total space P
* `IsLocalSection`: A smooth local section of the bundle

## Main results

* `IsPrincipalBundle.is_transitive`: The G-action is transitive on each fiber
* `contMDiffAt_gaugeMap`: The transition function between two local sections is smooth

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
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
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

class IsPrincipalBundle
    {B : Type*} [TopologicalSpace B]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
    (G : Type*) [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [Group G]
    (P : Type*) [TopologicalSpace P]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP]
    (IP : ModelWithCorners ℝ EP HP) [ChartedSpace HP P]
    [MulAction (MulOpposite G) P]
    (proj : P → B) where
  is_free : ∀ (p : P), MulAction.stabilizer (MulOpposite G) p = ⊥
  respects_fibres : ∀ (p : P) (g : G), proj (p <• g) = proj p
  smooth_proj : ContMDiff IP IB ∞ proj
  localTriv : P → Trivialization G proj
  mem_baseSet_localTriv : ∀ p, proj p ∈ (localTriv p).baseSet
  /-- Each local trivialization is `G`-equivariant on its whole source, intertwining the
  torsor action on the fibres with right translation of `G` on itself. -/
  equivariant_localTriv : ∀ (p q : P), q ∈ (localTriv p).source → ∀ (g : G),
    (localTriv p) (q <• g) = ⟨proj q, ((localTriv p) q).2 * g⟩
  /-- Each local trivialization is smooth on its source. Together with `smooth_proj` and
  equivariance this makes `localTriv p` the smooth equivariant chart of Tu §27. -/
  smooth_localTriv : ∀ p : P,
    ContMDiffOn IP (IB.prod IG) ∞ (localTriv p) (localTriv p).source

variable [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
theorem IsPrincipalBundle.is_transitive
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (b : B) (p q : P)
    (hp : proj p = b) (hq : proj q = b) :
    q ∈ MulAction.orbit (MulOpposite G) p := by
  set φ := hPB.localTriv p
  have hmem_p : proj p ∈ φ.baseSet := hPB.mem_baseSet_localTriv p
  set g := (φ p).2⁻¹ * (φ q).2
  refine ⟨MulOpposite.op g, φ.injOn ?_ ?_ ?_⟩
  · rw [Trivialization.mem_source]
    rw [hPB.respects_fibres p g]
    exact hmem_p
  · rw [φ.mem_source]
    rw [hq]; rw [hp] at hmem_p; exact hmem_p
  · have heq := hPB.equivariant_localTriv p p (φ.mem_source.mpr hmem_p) g
    simp only [Trivialization.coe_coe] at heq ⊢
    rw [heq, show g = (φ p).2⁻¹ * (φ q).2 from rfl, mul_inv_cancel_left]
    have hq_src : q ∈ φ.source := by
      rw [φ.mem_source, hq]; rw [hp] at hmem_p; exact hmem_p
    rw [show proj p = proj q from by rw [hp, hq], ← φ.coe_fst hq_src, Prod.mk.eta]

def IsLocalSection (σ : B → P) (U : Set B) : Prop :=
  IsOpen U ∧
  ContMDiffOn IB (IB.prod IG) ∞ σ U ∧
  ∀ m ∈ U, proj (σ m) = m

omit [IsManifold IB ∞ B]
     [T2Space G]
     [CompleteSpace EG]
     [BoundarylessManifold IG G] in
lemma gaugeMap_exists
    (σ₁ σ₂ : B → P)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ∃ g : G, σ₂ m = σ₁ m <• g := by
  have h1 : proj (σ₁ m) = m := hσ₁.2.2 m hm.1
  have h2 : proj (σ₂ m) = m := hσ₂.2.2 m hm.2
  have hmem : σ₂ m ∈ MulAction.orbit (MulOpposite G) (σ₁ m) :=
    IsPrincipalBundle.is_transitive (IB := IB) (IG := IG) (P := P) m (σ₁ m) (σ₂ m) h1 h2
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact ⟨MulOpposite.unop g, by rw [← hg]; simp [HSMul.hSMul]⟩

set_option linter.unusedSectionVars false in
omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma gaugeMap_unique
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (σ₁ σ₂ : B → P)
    (m : B) (g h : G)
    (hg : σ₁ m <• g = σ₂ m)
    (hh : σ₁ m <• h = σ₂ m) :
    g = h := by
  have heq : σ₁ m <• g = σ₁ m <• h := hg.trans hh.symm
  have haction : σ₁ m <• (g * h⁻¹) = σ₁ m := by
    simp only [MulOpposite.op_mul, mul_smul]
    rw [heq]
    simp only [MulOpposite.op_inv, inv_smul_smul]
  have hone : MulOpposite.op (g * h⁻¹) ∈
      MulAction.stabilizer (MulOpposite G) (σ₁ m) := by
    simp only [MulAction.mem_stabilizer_iff, haction]
  rw [hPB.is_free (σ₁ m)] at hone
  exact eq_of_mul_inv_eq_one (MulOpposite.op_injective hone)

/-- The transition function between two local sections of a smooth principal bundle is smooth. -/
theorem contMDiffAt_gaugeMap
    {B : Type*} [TopologicalSpace B]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HB B]
    [IsManifold IB ∞ B]
    {G : Type*} [TopologicalSpace G] [T2Space G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
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
    (σ₁ σ₂ : B → P)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (Ω : B → G)
    (hΩ : ∀ x ∈ U₁ ∩ U₂, σ₁ x <• Ω x = σ₂ x)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ContMDiffAt IB IG ∞ Ω m := by
  set φ := hPB.localTriv (σ₁ m)
  have hb : m ∈ φ.baseSet := by
    have h := hPB.mem_baseSet_localTriv (σ₁ m)
    rwa [hσ₁.2.2 m hm.1] at h
  have hV : IsOpen (U₁ ∩ U₂ ∩ φ.baseSet) := (hσ₁.1.inter hσ₂.1).inter φ.open_baseSet
  have hmV : m ∈ U₁ ∩ U₂ ∩ φ.baseSet := ⟨hm, hb⟩
  have hsrc₁ : ∀ x ∈ U₁ ∩ U₂ ∩ φ.baseSet, σ₁ x ∈ φ.source := fun x hx ↦
    φ.mem_source.mpr (by rw [hσ₁.2.2 x hx.1.1]; exact hx.2)
  have hsrc₂ : ∀ x ∈ U₁ ∩ U₂ ∩ φ.baseSet, σ₂ x ∈ φ.source := fun x hx ↦
    φ.mem_source.mpr (by rw [hσ₂.2.2 x hx.1.2]; exact hx.2)
  -- the closed form for Ω on the common neighbourhood
  have hkey : ∀ x ∈ U₁ ∩ U₂ ∩ φ.baseSet,
      Ω x = ((φ (σ₁ x)).2)⁻¹ * (φ (σ₂ x)).2 := by
    intro x hx
    have h := hPB.equivariant_localTriv (σ₁ m) (σ₁ x) (hsrc₁ x hx) (Ω x)
    rw [hΩ x hx.1] at h
    have h2 : (φ (σ₂ x)).2 = (φ (σ₁ x)).2 * Ω x := by rw [h]
    rw [h2, inv_mul_cancel_left]
  -- smoothness of the right-hand side
  have hσ₁m : ContMDiffAt IB (IB.prod IG) ∞ σ₁ m :=
    hσ₁.2.1.contMDiffAt (hσ₁.1.mem_nhds hm.1)
  have hσ₂m : ContMDiffAt IB (IB.prod IG) ∞ σ₂ m :=
    hσ₂.2.1.contMDiffAt (hσ₂.1.mem_nhds hm.2)
  have hφ₁ : ContMDiffAt IB (IB.prod IG) ∞ (fun x ↦ φ (σ₁ x)) m :=
    ((hPB.smooth_localTriv (σ₁ m)).contMDiffAt
      (φ.open_source.mem_nhds (hsrc₁ m hmV))).comp m hσ₁m
  have hφ₂ : ContMDiffAt IB (IB.prod IG) ∞ (fun x ↦ φ (σ₂ x)) m :=
    ((hPB.smooth_localTriv (σ₁ m)).contMDiffAt
      (φ.open_source.mem_nhds (hsrc₂ m hmV))).comp m hσ₂m
  have hg₁ : ContMDiffAt IB IG ∞ (fun x ↦ (φ (σ₁ x)).2) m :=
    contMDiff_snd.contMDiffAt.comp m hφ₁
  have hg₂ : ContMDiffAt IB IG ∞ (fun x ↦ (φ (σ₂ x)).2) m :=
    contMDiff_snd.contMDiffAt.comp m hφ₂
  exact (hg₁.inv.mul hg₂).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hV.mem_nhds hmV) hkey)

end
