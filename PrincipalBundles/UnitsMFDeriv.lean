/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib

/-!
# Manifold derivatives of multiplication on the units of a normed algebra

The group of units `Fˣ` of a complete normed `ℝ`-algebra `F` is a Lie group modelled on `F`
(via the open embedding `Units.val`).  This file computes the manifold derivatives of left
multiplication and of two-sided multiplication (conjugation) on `Fˣ`, which specialise to the
Maurer–Cartan form and the adjoint representation for the frame bundle.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

section Units

variable {F : Type*} [NormedRing F] [CompleteSpace F] [NormedAlgebra ℝ F]

/-- The chart of `Fˣ` is `Units.val` (`Units.chartAt_apply`, `Units.chartAt_source`), so near `g`
the coordinate expression of a map `f : Fˣ → Fˣ` agrees with any `φ : F → F` extending
`h ↦ (f h : F)`. -/
lemma units_writtenInExtChartAt_eventuallyEq (f : Fˣ → Fˣ) (φ : F → F)
    (hφ : ∀ h : Fˣ, ((f h : Fˣ) : F) = φ h) (g : Fˣ) :
    writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F) g f =ᶠ[nhds (g : F)] φ := by
  filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds (Set.mem_range_self g)]
    with x hx
  obtain ⟨y, rfl⟩ := hx
  have hs : (extChartAt 𝓘(ℝ, F) g).symm (y : F) = y :=
    (extChartAt 𝓘(ℝ, F) g).left_inv
      (by rw [extChartAt_source, Units.chartAt_source]; exact Set.mem_univ y)
  simp only [writtenInExtChartAt, Function.comp_apply, hs]
  exact hφ y

/-- The manifold derivative of left multiplication `h ↦ a * h` on `Fˣ`, computed at any point
`g`, is left multiplication by `a.val` on the model space `F`. -/
lemma mfderiv_units_mulLeft (a g : Fˣ) (v : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h) g v = (a : F) * v := by
  have hd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h) g :=
    ((contMDiff_mul_left (n := 1) (a := a)).mdifferentiable one_ne_zero).mdifferentiableAt
  have hw := units_writtenInExtChartAt_eventuallyEq (fun h : Fˣ => a * h)
    (ContinuousLinearMap.mul ℝ F (a : F)) (fun h => by simp) g
  rw [hd.mfderiv_abuse]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rw [show extChartAt 𝓘(ℝ, F) g g = (g : F) from rfl, hw.fderiv_eq, ContinuousLinearMap.fderiv]
  simp

/-- The manifold derivative of the two-sided multiplication `h ↦ a * h * b` on `Fˣ`, computed at
the identity, is `v ↦ a.val * v * b.val` on the model space `F`. -/
lemma mfderiv_units_mul_mul (a b : Fˣ) (A : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h * b) 1 A = (a : F) * A * (b : F) := by
  have hd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun h : Fˣ => a * h * b) 1 :=
    (((contMDiff_mul_left (n := 1) (a := a)).mul (contMDiff_const (c := b))).mdifferentiable
      one_ne_zero).mdifferentiableAt
  have hw := units_writtenInExtChartAt_eventuallyEq (fun h : Fˣ => a * h * b)
    ((ContinuousLinearMap.mul ℝ F (a : F)).comp ((ContinuousLinearMap.mul ℝ F).flip (b : F)))
    (fun h => by simp [mul_assoc]) 1
  rw [hd.mfderiv_abuse]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rw [show extChartAt 𝓘(ℝ, F) (1 : Fˣ) 1 = ((1 : Fˣ) : F) from rfl, hw.fderiv_eq,
    ContinuousLinearMap.fderiv]
  simp [mul_assoc]

end Units
