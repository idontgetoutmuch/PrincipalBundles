/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import PrincipalBundles.PrincipalBundle

/-!
# The Hopf fibration as a principal circle bundle

The Hopf fibration `S¹ → S³ → S²` (Sharpe, *Differential Geometry*, Chapter 1, Example 3.14).

* `S³` is the unit sphere in `ℝ⁴ = ℂ²`, with complex coordinates `w₀ = x₀ + i x₁` and
  `w₁ = x₂ + i x₃`, and Mathlib's stereographic charts.
* The circle acts on the right by `(w₀, w₁) ⬝ λ = (w₀ λ, w₁ λ)`.
* The Hopf map `π : S³ → S²` is `π(w₀, w₁) = (2 w₀ w̄₁, |w₀|² - |w₁|²) ∈ ℂ × ℝ = ℝ³`.

The main result is `instIsPrincipalBundle`. Its local trivialisations are `triv₀` over
`{w₀ ≠ 0}` and `triv₁` over `{w₁ ≠ 0}`, each sending a point to its image under `hopf`
together with the phase of the nonzero coordinate.
-/

open Set Metric Bundle RightActions ComplexConjugate
open scoped Manifold ContDiff

noncomputable section

namespace Hopf

/-- The 3-sphere, the unit sphere in `ℝ⁴`. -/
abbrev S3 : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The 2-sphere, the unit sphere in `ℝ³`. -/
abbrev S2 : Type := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The first complex coordinate `w₀ = x₀ + i x₁` of a point of `ℝ⁴`. -/
def w₀ (x : EuclideanSpace ℝ (Fin 4)) : ℂ := ⟨x 0, x 1⟩

/-- The second complex coordinate `w₁ = x₂ + i x₃` of a point of `ℝ⁴`. -/
def w₁ (x : EuclideanSpace ℝ (Fin 4)) : ℂ := ⟨x 2, x 3⟩

/-- The point of `ℝ⁴` with complex coordinates `(z, w)`. -/
def ofPair (z w : ℂ) : EuclideanSpace ℝ (Fin 4) := !₂[z.re, z.im, w.re, w.im]

lemma norm_sq_eq (x : EuclideanSpace ℝ (Fin 4)) :
    ‖x‖ ^ 2 = ‖w₀ x‖ ^ 2 + ‖w₁ x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp [w₀, w₁, sq]
  ring

lemma norm_sq_ofPair (z w : ℂ) : ‖ofPair z w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp [ofPair, sq]
  ring

/-! ### The circle action -/

lemma ofPair_mul_mem_sphere (x : S3) (g : Circle) :
    ofPair (w₀ x * g) (w₁ x * g) ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have hx := norm_sq_eq x
  have h1 : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simp
  rw [mem_sphere_zero_iff_norm]
  have : ‖ofPair (w₀ x * g) (w₁ x * g)‖ ^ 2 = 1 := by
    rw [norm_sq_ofPair, norm_mul, norm_mul, Circle.norm_coe, mul_one, mul_one, ← hx, h1, one_pow]
  nlinarith [norm_nonneg (ofPair (w₀ x * g) (w₁ x * g))]

@[simp] lemma w₀_ofPair (z w : ℂ) : w₀ (ofPair z w) = z := by
  apply Complex.ext <;> simp [w₀, ofPair]

@[simp] lemma w₁_ofPair (z w : ℂ) : w₁ (ofPair z w) = w := by
  apply Complex.ext <;> simp [w₁, ofPair]

lemma ofPair_w (x : EuclideanSpace ℝ (Fin 4)) : ofPair (w₀ x) (w₁ x) = x := by
  ext i; fin_cases i <;> simp [ofPair, w₀, w₁]

/-- The right action of the circle on `S³`: `(w₀, w₁) ⬝ λ = (w₀ λ, w₁ λ)`. -/
instance : MulAction (MulOpposite Circle) S3 where
  smul g x := ⟨ofPair (w₀ x * g.unop) (w₁ x * g.unop), ofPair_mul_mem_sphere x g.unop⟩
  one_smul := by
    intro x
    apply Subtype.ext
    change ofPair (w₀ x * ((1 : Circleᵐᵒᵖ).unop : ℂ)) (w₁ x * ((1 : Circleᵐᵒᵖ).unop : ℂ)) = x
    simp [ofPair_w]
  mul_smul := by
    intro g h x
    apply Subtype.ext
    change ofPair (w₀ x * ((g * h).unop : ℂ)) (w₁ x * ((g * h).unop : ℂ)) =
      ofPair (w₀ (ofPair (w₀ x * (h.unop : ℂ)) (w₁ x * (h.unop : ℂ))) * (g.unop : ℂ))
        (w₁ (ofPair (w₀ x * (h.unop : ℂ)) (w₁ x * (h.unop : ℂ))) * (g.unop : ℂ))
    simp [mul_assoc]

lemma coe_smul (g : Circleᵐᵒᵖ) (x : S3) :
    ((g • x : S3) : EuclideanSpace ℝ (Fin 4)) = ofPair (w₀ x * g.unop) (w₁ x * g.unop) := rfl

/-! ### The Hopf map -/

/-- The Hopf map on `ℝ⁴`: `(w₀, w₁) ↦ (2 w₀ w̄₁, |w₀|² - |w₁|²)`. -/
def hopfVec (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * (w₀ x * conj (w₁ x)).re, 2 * (w₀ x * conj (w₁ x)).im, ‖w₀ x‖ ^ 2 - ‖w₁ x‖ ^ 2]

lemma norm_sq_hopfVec (x : EuclideanSpace ℝ (Fin 4)) : ‖hopfVec x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by
  rw [norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [hopfVec, Complex.sq_norm, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  simp [w₀, w₁]
  ring

lemma hopfVec_mem_sphere (x : S3) : hopfVec x ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have h1 : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simp
  have h := norm_sq_hopfVec x
  rw [h1] at h
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (hopfVec x)]

/-- The Hopf map `π : S³ → S²`. -/
def hopf (x : S3) : S2 := ⟨hopfVec x, hopfVec_mem_sphere x⟩

/-! ### Smoothness helpers -/

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : WithTop ℕ∞}

lemma w₀_eq (x : EuclideanSpace ℝ (Fin 4)) :
    w₀ x = Complex.ofRealCLM (x 0) + Complex.ofRealCLM (x 1) * Complex.I := by
  apply Complex.ext <;> simp [w₀]

lemma w₁_eq (x : EuclideanSpace ℝ (Fin 4)) :
    w₁ x = Complex.ofRealCLM (x 2) + Complex.ofRealCLM (x 3) * Complex.I := by
  apply Complex.ext <;> simp [w₁]

lemma contDiff_w₀ : ContDiff ℝ k w₀ := by
  have h : w₀ = fun x => Complex.ofRealCLM (x 0) + Complex.ofRealCLM (x 1) * Complex.I :=
    funext w₀_eq
  rw [h]
  refine ContDiff.add ?_ (ContDiff.mul ?_ contDiff_const)
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2)
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2)

lemma contDiff_w₁ : ContDiff ℝ k w₁ := by
  have h : w₁ = fun x => Complex.ofRealCLM (x 2) + Complex.ofRealCLM (x 3) * Complex.I :=
    funext w₁_eq
  rw [h]
  refine ContDiff.add ?_ (ContDiff.mul ?_ contDiff_const)
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2)
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2)

lemma ContDiff.ofPair' {f g : V → ℂ} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun v => ofPair (f v) (g v)) := by
  have hre : ∀ {h : V → ℂ}, ContDiff ℝ k h → ContDiff ℝ k (fun v => (h v).re) := by
    intro h hh
    have := Complex.reCLM.contDiff.comp hh
    simp only [Function.comp_def, Complex.reCLM_apply] at this
    exact this
  have him : ∀ {h : V → ℂ}, ContDiff ℝ k h → ContDiff ℝ k (fun v => (h v).im) := by
    intro h hh
    have := Complex.imCLM.contDiff.comp hh
    simp only [Function.comp_def, Complex.imCLM_apply] at this
    exact this
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa [ofPair] using hre hf
  · simpa [ofPair] using him hf
  · simpa [ofPair] using hre hg
  · simpa [ofPair] using him hg

end Smooth

lemma contMDiff_smul_map :
    ContMDiff ((𝓡 3).prod (𝓡 1)) (𝓡 3) ∞ (fun p : S3 × Circle => p.1 <• p.2) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hF : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 4) × ℂ =>
      ofPair (w₀ p.1 * p.2) (w₁ p.1 * p.2)) := by
    exact ContDiff.ofPair' ((contDiff_w₀.comp contDiff_fst).mul contDiff_snd)
      ((contDiff_w₁.comp contDiff_fst).mul contDiff_snd)
  have hc : ContMDiff ((𝓡 3).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × ℂ) ∞
      (fun p : S3 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 4)), (p.2 : ℂ))) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space
      (contMDiff_coe_sphere.comp contMDiff_snd)
  exact (hF.contMDiff.comp hc).codRestrict_sphere (n := 3)
    (fun p => ofPair_mul_mem_sphere p.1 p.2)

/-! ### Sphere-valued maps that are smooth on an open set -/

section SphereOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

lemma contMDiffOn_sphere_of_coe {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {f : M → sphere (0 : E) 1} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, E) m (fun x => (f x : E)) U) :
    ContMDiffOn I (𝓡 n) m f U := by
  intro x hx
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have h1 : ContMDiff I 𝓘(ℝ, E) m (fun y : V => (f y : E)) :=
    hf.comp_contMDiff contMDiff_subtype_val (fun y => y.2)
  have h2 : ContMDiff I (𝓡 n) m (fun y : V => f y) := by
    have := h1.codRestrict_sphere (n := n) (fun y => (f y).2)
    exact this
  have h3 : ContMDiffAt I (𝓡 n) m f x :=
    (contMDiffAt_subtype_iff (U := V) (x := ⟨x, hx⟩)).mp (h2 ⟨x, hx⟩)
  exact h3.contMDiffWithinAt

end SphereOn

/-! ### Coordinates on `ℝ³` and the phase map -/

/-- The complex coordinate `b₀ + i b₁` of a point of `ℝ³`. -/
def β (b : EuclideanSpace ℝ (Fin 3)) : ℂ := ⟨b 0, b 1⟩

lemma norm_sq_E3 (b : EuclideanSpace ℝ (Fin 3)) : ‖b‖ ^ 2 = ‖β b‖ ^ 2 + b 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  simp [β, sq]

lemma S2_norm_sq (b : S2) : ‖β b‖ ^ 2 + (b : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
  rw [← norm_sq_E3]; simp

lemma S2_two_le (b : S2) : -1 ≤ (b : EuclideanSpace ℝ (Fin 3)) 2 ∧
    (b : EuclideanSpace ℝ (Fin 3)) 2 ≤ 1 := by
  have h := S2_norm_sq b
  have h0 := sq_nonneg ‖β b‖
  constructor <;> nlinarith

lemma S3_norm_sq (x : S3) : ‖w₀ x‖ ^ 2 + ‖w₁ x‖ ^ 2 = 1 := by
  rw [← norm_sq_eq]; simp

@[simp] lemma β_hopfVec (x : EuclideanSpace ℝ (Fin 4)) :
    β (hopfVec x) = 2 * (w₀ x * conj (w₁ x)) := by
  apply Complex.ext <;> simp [β, hopfVec]

@[simp] lemma hopfVec_two (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec x 2 = ‖w₀ x‖ ^ 2 - ‖w₁ x‖ ^ 2 := by
  simp [hopfVec]

lemma E3_ext {a b : EuclideanSpace ℝ (Fin 3)} (h1 : β a = β b) (h2 : a 2 = b 2) : a = b := by
  have h0 : a 0 = b 0 := by simpa [β] using congrArg Complex.re h1
  have h1' : a 1 = b 1 := by simpa [β] using congrArg Complex.im h1
  ext i; fin_cases i
  · exact h0
  · exact h1'
  · exact h2

lemma ofPair_inj {z w z' w' : ℂ} (h : ofPair z w = ofPair z' w') : z = z' ∧ w = w' := by
  have h0 := congrArg w₀ h
  have h1 := congrArg w₁ h
  simp only [w₀_ofPair, w₁_ofPair] at h0 h1
  exact ⟨h0, h1⟩

/-- The complex number `z / |z|`. -/
def phaseC (z : ℂ) : ℂ := z * ((‖z‖ : ℂ))⁻¹

lemma norm_phaseC {z : ℂ} (hz : z ≠ 0) : ‖phaseC z‖ = 1 := by
  have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [phaseC, norm_inv, this]

/-- The phase `z / |z|` of a complex number, as a point of the circle (junk value `1` at `0`). -/
def phase (z : ℂ) : Circle :=
  if h : z = 0 then 1 else ⟨phaseC z, mem_sphere_zero_iff_norm.mpr (norm_phaseC h)⟩

lemma coe_phase {z : ℂ} (hz : z ≠ 0) : (phase z : ℂ) = phaseC z := by
  simp [phase, hz]

lemma phase_mul_circle {z : ℂ} (hz : z ≠ 0) (g : Circle) : phase (z * g) = phase z * g := by
  have hg : (g : ℂ) ≠ 0 := Circle.coe_ne_zero g
  have hzg : z * g ≠ 0 := mul_ne_zero hz hg
  apply Circle.ext
  rw [Circle.coe_mul, coe_phase hzg, coe_phase hz]
  simp [phaseC]
  ring

/-- A retraction of `ℝ⁴` onto `S³` (junk value away from the sphere). -/
def toS3 (v : EuclideanSpace ℝ (Fin 4)) : S3 :=
  if h : ‖v‖ = 1 then ⟨v, mem_sphere_zero_iff_norm.mpr h⟩ else ⟨ofPair 1 0, by
    rw [mem_sphere_zero_iff_norm]
    have := norm_sq_ofPair 1 0
    simp only [norm_one, norm_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at this
    nlinarith [norm_nonneg (ofPair 1 0)]⟩

lemma coe_toS3 {v : EuclideanSpace ℝ (Fin 4)} (h : ‖v‖ = 1) : (toS3 v : EuclideanSpace ℝ (Fin 4)) = v := by
  simp [toS3, h]

/-! ### The trivialisation over `{w₀ ≠ 0}` : algebra -/

/-- `r₀(b) = √((1 + b₂)/2)`, which equals `|w₀|` on the fibre over `b`. -/
def r₀ (v : EuclideanSpace ℝ (Fin 3)) : ℝ := Real.sqrt ((1 + v 2) / 2)

/-- The inverse of the first trivialisation, as a map into `ℝ⁴`. -/
def inv₀Vec (v : EuclideanSpace ℝ (Fin 3)) (c : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  ofPair ((r₀ v : ℂ) * c) (conj (β v) * c / (2 * (r₀ v : ℂ)))

lemma r₀_sq {v : EuclideanSpace ℝ (Fin 3)} (h : -1 < v 2) : r₀ v ^ 2 = (1 + v 2) / 2 := by
  rw [r₀, Real.sq_sqrt]; linarith

lemma r₀_pos {v : EuclideanSpace ℝ (Fin 3)} (h : -1 < v 2) : 0 < r₀ v := by
  rw [r₀]; apply Real.sqrt_pos.mpr; linarith

lemma circle_mul_conj (g : Circle) : (g : ℂ) * conj (g : ℂ) = 1 := by
  simp [Complex.mul_conj']

lemma norm_inv₀Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ -1) (g : Circle) :
    ‖inv₀Vec b g‖ = 1 := by
  have hn := S2_norm_sq b
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : -1 < v 2 := lt_of_le_of_ne (S2_two_le b).1 (Ne.symm hb)
  have hr := r₀_pos ht
  have hr2 := r₀_sq ht
  have hsq : ‖inv₀Vec v g‖ ^ 2 = 1 := by
    rw [inv₀Vec, norm_sq_ofPair, norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_conj,
      Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_two]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (inv₀Vec v g)]

lemma hopfVec_inv₀Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ -1) (g : Circle) :
    hopfVec (inv₀Vec b g) = b := by
  have hn := S2_norm_sq b
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : -1 < v 2 := lt_of_le_of_ne (S2_two_le b).1 (Ne.symm hb)
  have hr := r₀_pos ht
  have hr2 := r₀_sq ht
  have hrC : (r₀ v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply E3_ext
  · rw [β_hopfVec, inv₀Vec, w₀_ofPair, w₁_ofPair]
    have hg := circle_mul_conj g
    simp only [map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_ofNat]
    field_simp
    linear_combination (β v) * hg
  · rw [hopfVec_two, inv₀Vec, w₀_ofPair, w₁_ofPair]
    rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_conj,
      Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_two]
    field_simp
    nlinarith

lemma phase_w₀_inv₀Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ -1) (g : Circle) :
    phase (w₀ (inv₀Vec b g)) = g := by
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : -1 < v 2 := lt_of_le_of_ne (S2_two_le b).1 (Ne.symm hb)
  have hr := r₀_pos ht
  have hrC : (r₀ v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [inv₀Vec, w₀_ofPair]
  apply Circle.ext
  rw [coe_phase (mul_ne_zero hrC (Circle.coe_ne_zero g)), phaseC, norm_mul, Circle.norm_coe,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  field_simp

lemma w₀_ne_zero_iff (x : S3) : w₀ x ≠ 0 ↔ hopfVec x 2 ≠ -1 := by
  have h := S3_norm_sq x
  rw [hopfVec_two, ne_eq, ← norm_eq_zero, ne_eq]
  constructor
  · intro h0 h1
    have : ‖w₀ x‖ ^ 2 = 0 := by linarith
    exact h0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  · intro h0 h1
    apply h0; rw [h1] at h ⊢; linarith

lemma inv₀Vec_hopf (x : S3) (hx : w₀ x ≠ 0) :
    inv₀Vec (hopfVec x) (phase (w₀ x)) = x := by
  have h := S3_norm_sq x
  set a := w₀ x
  set w := w₁ x
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr hx
  have hr : r₀ (hopfVec x) = ‖a‖ := by
    rw [r₀, hopfVec_two]
    rw [show (1 + (‖a‖ ^ 2 - ‖w‖ ^ 2)) / 2 = ‖a‖ ^ 2 by linarith]
    exact Real.sqrt_sq hna.le
  have haC : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hna.ne'
  conv_rhs => rw [← ofPair_w (x : EuclideanSpace ℝ (Fin 4))]
  rw [inv₀Vec, hr, coe_phase hx, β_hopfVec, phaseC]
  congr 1
  · field_simp
    rfl
  · have hc := Complex.conj_mul' a
    simp only [map_mul, map_ofNat, Complex.conj_conj]
    field_simp
    rw [← hc]
    ring

/-! ### The trivialisation over `{w₁ ≠ 0}` : algebra -/

/-- `r₁(b) = √((1 - b₂)/2)`, which equals `|w₁|` on the fibre over `b`. -/
def r₁ (v : EuclideanSpace ℝ (Fin 3)) : ℝ := Real.sqrt ((1 - v 2) / 2)

/-- The inverse of the second trivialisation, as a map into `ℝ⁴`. -/
def inv₁Vec (v : EuclideanSpace ℝ (Fin 3)) (c : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  ofPair (β v * c / (2 * (r₁ v : ℂ))) ((r₁ v : ℂ) * c)

lemma r₁_sq {v : EuclideanSpace ℝ (Fin 3)} (h : v 2 < 1) : r₁ v ^ 2 = (1 - v 2) / 2 := by
  rw [r₁, Real.sq_sqrt]; linarith

lemma r₁_pos {v : EuclideanSpace ℝ (Fin 3)} (h : v 2 < 1) : 0 < r₁ v := by
  rw [r₁]; apply Real.sqrt_pos.mpr; linarith

lemma norm_inv₁Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1) (g : Circle) :
    ‖inv₁Vec b g‖ = 1 := by
  have hn := S2_norm_sq b
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : v 2 < 1 := lt_of_le_of_ne (S2_two_le b).2 hb
  have hr := r₁_pos ht
  have hr2 := r₁_sq ht
  have hsq : ‖inv₁Vec v g‖ ^ 2 = 1 := by
    rw [inv₁Vec, norm_sq_ofPair, norm_mul, norm_div, norm_mul, norm_mul,
      Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_two]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (inv₁Vec v g)]

lemma hopfVec_inv₁Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1) (g : Circle) :
    hopfVec (inv₁Vec b g) = b := by
  have hn := S2_norm_sq b
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : v 2 < 1 := lt_of_le_of_ne (S2_two_le b).2 hb
  have hr := r₁_pos ht
  have hr2 := r₁_sq ht
  have hrC : (r₁ v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply E3_ext
  · rw [β_hopfVec, inv₁Vec, w₀_ofPair, w₁_ofPair]
    have hg := circle_mul_conj g
    simp only [map_mul, Complex.conj_ofReal]
    field_simp
    linear_combination (β v) * hg
  · rw [hopfVec_two, inv₁Vec, w₀_ofPair, w₁_ofPair]
    rw [norm_mul, norm_div, norm_mul, norm_mul,
      Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_two]
    field_simp
    nlinarith

lemma phase_w₁_inv₁Vec (b : S2) (hb : (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1) (g : Circle) :
    phase (w₁ (inv₁Vec b g)) = g := by
  set v : EuclideanSpace ℝ (Fin 3) := (b : EuclideanSpace ℝ (Fin 3))
  have ht : v 2 < 1 := lt_of_le_of_ne (S2_two_le b).2 hb
  have hr := r₁_pos ht
  have hrC : (r₁ v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [inv₁Vec, w₁_ofPair]
  apply Circle.ext
  rw [coe_phase (mul_ne_zero hrC (Circle.coe_ne_zero g)), phaseC, norm_mul, Circle.norm_coe,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  field_simp

lemma w₁_ne_zero_iff (x : S3) : w₁ x ≠ 0 ↔ hopfVec x 2 ≠ 1 := by
  have h := S3_norm_sq x
  rw [hopfVec_two, ne_eq, ← norm_eq_zero, ne_eq]
  constructor
  · intro h0 h1
    have : ‖w₁ x‖ ^ 2 = 0 := by linarith
    exact h0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  · intro h0 h1
    apply h0; rw [h1] at h ⊢; linarith

lemma inv₁Vec_hopf (x : S3) (hx : w₁ x ≠ 0) :
    inv₁Vec (hopfVec x) (phase (w₁ x)) = x := by
  have h := S3_norm_sq x
  set a := w₀ x
  set w := w₁ x
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hx
  have hr : r₁ (hopfVec x) = ‖w‖ := by
    rw [r₁, hopfVec_two]
    rw [show (1 - (‖a‖ ^ 2 - ‖w‖ ^ 2)) / 2 = ‖w‖ ^ 2 by linarith]
    exact Real.sqrt_sq hnw.le
  have hwC : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
  conv_rhs => rw [← ofPair_w (x : EuclideanSpace ℝ (Fin 4))]
  rw [inv₁Vec, hr, coe_phase hx, β_hopfVec, phaseC]
  congr 1
  · have hc := Complex.conj_mul' w
    field_simp
    rw [← hc]
    ring
  · field_simp
    rfl

/-! ### Smoothness of the pieces -/

lemma contDiff_hopfVec {k : WithTop ℕ∞} : ContDiff ℝ k hopfVec := by
  have hp : ContDiff ℝ k (fun x : EuclideanSpace ℝ (Fin 4) => w₀ x * conj (w₁ x)) :=
    contDiff_w₀.mul (Complex.conjCLE.contDiff.comp contDiff_w₁)
  have hn0 : ContDiff ℝ k (fun x : EuclideanSpace ℝ (Fin 4) => ‖w₀ x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_w₀
  have hn1 : ContDiff ℝ k (fun x : EuclideanSpace ℝ (Fin 4) => ‖w₁ x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_w₁
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa [hopfVec] using contDiff_const.mul (Complex.reCLM.contDiff.comp hp)
  · simpa [hopfVec] using contDiff_const.mul (Complex.imCLM.contDiff.comp hp)
  · simpa [hopfVec] using hn0.sub hn1

lemma contMDiff_hopf : ContMDiff (𝓡 3) (𝓡 2) ∞ hopf := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact (contDiff_hopfVec.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere (n := 2)
    (fun x => hopfVec_mem_sphere x)

lemma contDiffAt_phaseC {z : ℂ} (hz : z ≠ 0) {k : WithTop ℕ∞} : ContDiffAt ℝ k phaseC z := by
  have h1 : ContDiffAt ℝ k (fun z : ℂ => ((‖z‖ : ℂ))) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℝ hz)
  have h2 : ContDiffAt ℝ k (fun z : ℂ => ((‖z‖ : ℂ))⁻¹) z := by
    apply h1.inv
    exact_mod_cast norm_ne_zero_iff.mpr hz
  exact contDiffAt_id.mul h2

lemma contMDiffOn_phase_comp {f : S3 → ℂ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : Continuous f) :
    ContMDiffOn (𝓡 3) (𝓡 1) ∞ (fun x => phase (f x)) {x | f x ≠ 0} := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hU : IsOpen {x : S3 | f x ≠ 0} := isOpen_ne_fun hfc continuous_const
  apply contMDiffOn_sphere_of_coe (E := ℂ) (n := 1) hU
  have h : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun x => phaseC (f x)) {x | f x ≠ 0} := by
    intro x hx
    exact ((contDiffAt_phaseC hx).contMDiffAt.comp x (hf x)).contMDiffWithinAt
  refine h.congr ?_
  intro x hx
  exact coe_phase hx

lemma contMDiff_coe_S3 : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
    (fun x : S3 => (x : EuclideanSpace ℝ (Fin 4))) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact contMDiff_coe_sphere

lemma contMDiff_w₀_S3 : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun x : S3 => w₀ x) :=
  contDiff_w₀.contMDiff.comp contMDiff_coe_S3

lemma contMDiff_w₁_S3 : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun x : S3 => w₁ x) :=
  contDiff_w₁.contMDiff.comp contMDiff_coe_S3

lemma contDiffOn_inv₀Vec {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => inv₀Vec p.1 p.2)
      {p | -1 < p.1 2} := by
  intro p hp
  have hp' : (1 + p.1 2) / 2 ≠ 0 := by simp only [mem_setOf_eq] at hp; intro h; linarith
  have hlin : ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (1 + p.1 2) / 2) :=
    (contDiff_const.add ((contDiff_piLp_apply 2).comp contDiff_fst)).div_const _
  have hr : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (r₀ p.1 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((Real.contDiffAt_sqrt hp').comp p hlin.contDiffAt)
  have hβ : ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => conj (β p.1)) := by
    have : (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => conj (β p.1)) =
        fun p => Complex.ofRealCLM (p.1 0) - Complex.ofRealCLM (p.1 1) * Complex.I := by
      funext p; apply Complex.ext <;> simp [β]
    rw [this]
    exact (Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply 2).comp contDiff_fst)).sub
      ((Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply 2).comp contDiff_fst)).mul
        contDiff_const)
  have hrne : (r₀ p.1 : ℂ) ≠ 0 := by
    have := r₀_pos (v := p.1) hp
    exact_mod_cast this.ne'
  have h1 : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (r₀ p.1 : ℂ) * p.2) p :=
    hr.mul contDiffAt_snd
  have h2 : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ =>
      conj (β p.1) * p.2 / (2 * (r₀ p.1 : ℂ))) p :=
    by
      simp only [div_eq_mul_inv]
      exact (hβ.contDiffAt.mul contDiffAt_snd).mul
        ((contDiffAt_const.mul hr).inv (mul_ne_zero two_ne_zero hrne))
  have hO : ContDiff ℝ k (fun q : ℂ × ℂ => ofPair q.1 q.2) :=
    ContDiff.ofPair' contDiff_fst contDiff_snd
  exact (hO.contDiffAt.comp p (h1.prodMk h2)).contDiffWithinAt

lemma contDiffOn_inv₁Vec {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => inv₁Vec p.1 p.2)
      {p | p.1 2 < 1} := by
  intro p hp
  have hp' : (1 - p.1 2) / 2 ≠ 0 := by simp only [mem_setOf_eq] at hp; intro h; linarith
  have hlin : ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (1 - p.1 2) / 2) :=
    (contDiff_const.sub ((contDiff_piLp_apply 2).comp contDiff_fst)).div_const _
  have hr : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (r₁ p.1 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((Real.contDiffAt_sqrt hp').comp p hlin.contDiffAt)
  have hβ : ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => β p.1) := by
    have : (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => β p.1) =
        fun p => Complex.ofRealCLM (p.1 0) + Complex.ofRealCLM (p.1 1) * Complex.I := by
      funext p; apply Complex.ext <;> simp [β]
    rw [this]
    exact (Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply 2).comp contDiff_fst)).add
      ((Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply 2).comp contDiff_fst)).mul
        contDiff_const)
  have hrne : (r₁ p.1 : ℂ) ≠ 0 := by
    have := r₁_pos (v := p.1) hp
    exact_mod_cast this.ne'
  have h1 : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ => (r₁ p.1 : ℂ) * p.2) p :=
    hr.mul contDiffAt_snd
  have h2 : ContDiffAt ℝ k (fun p : EuclideanSpace ℝ (Fin 3) × ℂ =>
      β p.1 * p.2 / (2 * (r₁ p.1 : ℂ))) p :=
    by
      simp only [div_eq_mul_inv]
      exact (hβ.contDiffAt.mul contDiffAt_snd).mul
        ((contDiffAt_const.mul hr).inv (mul_ne_zero two_ne_zero hrne))
  have hO : ContDiff ℝ k (fun q : ℂ × ℂ => ofPair q.1 q.2) :=
    ContDiff.ofPair' contDiff_fst contDiff_snd
  exact (hO.contDiffAt.comp p (h2.prodMk h1)).contDiffWithinAt

/-! ### The two trivialisations -/

/-- Base set of the first trivialisation: `{b ∈ S² | b₂ ≠ -1}`, the image of `{w₀ ≠ 0}`. -/
def baseSet₀ : Set S2 := {b | (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ -1}

/-- Base set of the second trivialisation: `{b ∈ S² | b₂ ≠ 1}`, the image of `{w₁ ≠ 0}`. -/
def baseSet₁ : Set S2 := {b | (b : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1}

lemma continuous_coord2 : Continuous (fun b : S2 => (b : EuclideanSpace ℝ (Fin 3)) 2) :=
  (continuous_apply 2).comp (PiLp.continuous_ofLp 2 _ |>.comp continuous_subtype_val)

lemma isOpen_baseSet₀ : IsOpen baseSet₀ :=
  isOpen_ne_fun continuous_coord2 continuous_const

lemma isOpen_baseSet₁ : IsOpen baseSet₁ :=
  isOpen_ne_fun continuous_coord2 continuous_const

lemma mem_preimage_baseSet₀ (x : S3) : x ∈ hopf ⁻¹' baseSet₀ ↔ w₀ x ≠ 0 := by
  rw [w₀_ne_zero_iff]; rfl

lemma mem_preimage_baseSet₁ (x : S3) : x ∈ hopf ⁻¹' baseSet₁ ↔ w₁ x ≠ 0 := by
  rw [w₁_ne_zero_iff]; rfl

/-- The forward map of the first trivialisation. -/
def triv₀Fun (x : S3) : S2 × Circle := (hopf x, phase (w₀ x))

/-- The inverse map of the first trivialisation. -/
def triv₀Inv (p : S2 × Circle) : S3 := toS3 (inv₀Vec p.1 p.2)

/-- The forward map of the second trivialisation. -/
def triv₁Fun (x : S3) : S2 × Circle := (hopf x, phase (w₁ x))

/-- The inverse map of the second trivialisation. -/
def triv₁Inv (p : S2 × Circle) : S3 := toS3 (inv₁Vec p.1 p.2)

lemma coe_triv₀Inv {p : S2 × Circle} (hp : p.1 ∈ baseSet₀) :
    (triv₀Inv p : EuclideanSpace ℝ (Fin 4)) = inv₀Vec p.1 p.2 :=
  coe_toS3 (norm_inv₀Vec p.1 hp p.2)

lemma coe_triv₁Inv {p : S2 × Circle} (hp : p.1 ∈ baseSet₁) :
    (triv₁Inv p : EuclideanSpace ℝ (Fin 4)) = inv₁Vec p.1 p.2 :=
  coe_toS3 (norm_inv₁Vec p.1 hp p.2)

lemma contMDiffOn_triv₀Fun :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ triv₀Fun (hopf ⁻¹' baseSet₀) := by
  have h := contMDiffOn_phase_comp contMDiff_w₀_S3 contMDiff_w₀_S3.continuous
  have hs : hopf ⁻¹' baseSet₀ = {x : S3 | w₀ x ≠ 0} := by
    ext x; exact mem_preimage_baseSet₀ x
  rw [hs]
  exact contMDiff_hopf.contMDiffOn.prodMk h

lemma contMDiffOn_triv₁Fun :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ triv₁Fun (hopf ⁻¹' baseSet₁) := by
  have h := contMDiffOn_phase_comp contMDiff_w₁_S3 contMDiff_w₁_S3.continuous
  have hs : hopf ⁻¹' baseSet₁ = {x : S3 | w₁ x ≠ 0} := by
    ext x; exact mem_preimage_baseSet₁ x
  rw [hs]
  exact contMDiff_hopf.contMDiffOn.prodMk h

lemma contMDiff_coe_pair : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℂ) ∞
    (fun p : S2 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 3)), (p.2 : ℂ))) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space
    (contMDiff_coe_sphere.comp contMDiff_snd)

lemma contMDiffOn_triv₀Inv :
    ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ triv₀Inv (baseSet₀ ×ˢ univ) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  apply contMDiffOn_sphere_of_coe (n := 3) (isOpen_baseSet₀.prod isOpen_univ)
  have hv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun q : EuclideanSpace ℝ (Fin 3) × ℂ => inv₀Vec q.1 q.2) {p | -1 < p.1 2} :=
    contDiffOn_inv₀Vec.contMDiffOn
  have hc : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℂ) ∞
      (fun p : S2 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 3)), (p.2 : ℂ)))
      (baseSet₀ ×ˢ univ) :=
    contMDiff_coe_pair.contMDiffOn
  have hmaps : Set.MapsTo (fun p : S2 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 3)), (p.2 : ℂ)))
      (baseSet₀ ×ˢ univ) {p | -1 < p.1 2} := by
    intro p hp
    exact lt_of_le_of_ne (S2_two_le p.1).1 (Ne.symm hp.1)
  have h : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun p : S2 × Circle => inv₀Vec p.1 p.2) (baseSet₀ ×ˢ univ) :=
    hv.comp hc hmaps
  refine h.congr ?_
  intro p hp
  exact coe_triv₀Inv hp.1

set_option maxHeartbeats 400000 in
lemma contMDiffOn_triv₁Inv :
    ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ triv₁Inv (baseSet₁ ×ˢ univ) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  apply contMDiffOn_sphere_of_coe (n := 3) (isOpen_baseSet₁.prod isOpen_univ)
  have hv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun q : EuclideanSpace ℝ (Fin 3) × ℂ => inv₁Vec q.1 q.2) {p | p.1 2 < 1} :=
    contDiffOn_inv₁Vec.contMDiffOn
  have hc : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℂ) ∞
      (fun p : S2 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 3)), (p.2 : ℂ)))
      (baseSet₁ ×ˢ univ) :=
    contMDiff_coe_pair.contMDiffOn
  have hmaps : Set.MapsTo (fun p : S2 × Circle => ((p.1 : EuclideanSpace ℝ (Fin 3)), (p.2 : ℂ)))
      (baseSet₁ ×ˢ univ) {p | p.1 2 < 1} := by
    intro p hp
    exact lt_of_le_of_ne (S2_two_le p.1).2 hp.1
  have h : ContMDiffOn ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun p : S2 × Circle => inv₁Vec p.1 p.2) (baseSet₁ ×ˢ univ) :=
    hv.comp hc hmaps
  refine h.congr ?_
  intro p hp
  exact coe_triv₁Inv hp.1

lemma hopf_triv₀Inv {p : S2 × Circle} (hp : p.1 ∈ baseSet₀) : hopf (triv₀Inv p) = p.1 :=
  Subtype.ext (by
    change hopfVec (triv₀Inv p : EuclideanSpace ℝ (Fin 4)) = _
    rw [coe_triv₀Inv hp, hopfVec_inv₀Vec _ hp])

lemma hopf_triv₁Inv {p : S2 × Circle} (hp : p.1 ∈ baseSet₁) : hopf (triv₁Inv p) = p.1 :=
  Subtype.ext (by
    change hopfVec (triv₁Inv p : EuclideanSpace ℝ (Fin 4)) = _
    rw [coe_triv₁Inv hp, hopfVec_inv₁Vec _ hp])

/-- The local trivialisation of the Hopf map over `{w₀ ≠ 0}`:
`x ↦ (hopf x, w₀ x / |w₀ x|)`. -/
def triv₀ : Trivialization Circle hopf where
  toFun := triv₀Fun
  invFun := triv₀Inv
  source := hopf ⁻¹' baseSet₀
  target := baseSet₀ ×ˢ univ
  map_source' := fun _ hx => ⟨hx, trivial⟩
  map_target' := fun p hp => by
    change hopf (triv₀Inv p) ∈ baseSet₀
    rw [hopf_triv₀Inv hp.1]; exact hp.1
  left_inv' := fun x hx => by
    have hx' : w₀ x ≠ 0 := (mem_preimage_baseSet₀ x).mp hx
    apply Subtype.ext
    change (triv₀Inv (hopf x, phase (w₀ x)) : EuclideanSpace ℝ (Fin 4)) = x
    rw [coe_triv₀Inv (p := (hopf x, phase (w₀ x))) hx]
    exact inv₀Vec_hopf x hx'
  right_inv' := fun p hp => by
    change (hopf (triv₀Inv p), phase (w₀ (triv₀Inv p))) = p
    rw [hopf_triv₀Inv hp.1, coe_triv₀Inv hp.1, phase_w₀_inv₀Vec _ hp.1]
  open_source := isOpen_baseSet₀.preimage contMDiff_hopf.continuous
  open_target := isOpen_baseSet₀.prod isOpen_univ
  continuousOn_toFun := contMDiffOn_triv₀Fun.continuousOn
  continuousOn_invFun := contMDiffOn_triv₀Inv.continuousOn
  baseSet := baseSet₀
  open_baseSet := isOpen_baseSet₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ => rfl

/-- The local trivialisation of the Hopf map over `{w₁ ≠ 0}`:
`x ↦ (hopf x, w₁ x / |w₁ x|)`. -/
def triv₁ : Trivialization Circle hopf where
  toFun := triv₁Fun
  invFun := triv₁Inv
  source := hopf ⁻¹' baseSet₁
  target := baseSet₁ ×ˢ univ
  map_source' := fun _ hx => ⟨hx, trivial⟩
  map_target' := fun p hp => by
    change hopf (triv₁Inv p) ∈ baseSet₁
    rw [hopf_triv₁Inv hp.1]; exact hp.1
  left_inv' := fun x hx => by
    have hx' : w₁ x ≠ 0 := (mem_preimage_baseSet₁ x).mp hx
    apply Subtype.ext
    change (triv₁Inv (hopf x, phase (w₁ x)) : EuclideanSpace ℝ (Fin 4)) = x
    rw [coe_triv₁Inv (p := (hopf x, phase (w₁ x))) hx]
    exact inv₁Vec_hopf x hx'
  right_inv' := fun p hp => by
    change (hopf (triv₁Inv p), phase (w₁ (triv₁Inv p))) = p
    rw [hopf_triv₁Inv hp.1, coe_triv₁Inv hp.1, phase_w₁_inv₁Vec _ hp.1]
  open_source := isOpen_baseSet₁.preimage contMDiff_hopf.continuous
  open_target := isOpen_baseSet₁.prod isOpen_univ
  continuousOn_toFun := contMDiffOn_triv₁Fun.continuousOn
  continuousOn_invFun := contMDiffOn_triv₁Inv.continuousOn
  baseSet := baseSet₁
  open_baseSet := isOpen_baseSet₁
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ => rfl

lemma baseSet₀_union_baseSet₁ (b : S2) : b ∈ baseSet₀ ∨ b ∈ baseSet₁ := by
  by_cases h : (b : EuclideanSpace ℝ (Fin 3)) 2 = -1
  · right; change _ ≠ _; rw [h]; norm_num
  · left; exact h

/-! ### Equivariance -/

@[simp] lemma w₀_smul (x : S3) (g : Circle) :
    w₀ ((x <• g : S3) : EuclideanSpace ℝ (Fin 4)) = w₀ x * g := by
  change w₀ (ofPair _ _) = _; simp

@[simp] lemma w₁_smul (x : S3) (g : Circle) :
    w₁ ((x <• g : S3) : EuclideanSpace ℝ (Fin 4)) = w₁ x * g := by
  change w₁ (ofPair _ _) = _; simp

lemma hopf_smul (x : S3) (g : Circle) : hopf (x <• g) = hopf x := by
  have hg := circle_mul_conj g
  apply Subtype.ext
  change hopfVec ((x <• g : S3) : EuclideanSpace ℝ (Fin 4)) = hopfVec x
  apply E3_ext
  · rw [β_hopfVec, β_hopfVec, w₀_smul, w₁_smul, map_mul]
    linear_combination (2 * w₀ x * conj (w₁ x)) * hg
  · rw [hopfVec_two, hopfVec_two, w₀_smul, w₁_smul, norm_mul, norm_mul, Circle.norm_coe,
      mul_one, mul_one]

lemma triv₀_smul (x : S3) (hx : w₀ x ≠ 0) (g : Circle) :
    triv₀ (x <• g) = (hopf x, (triv₀ x).2 * g) := by
  change (hopf (x <• g), phase (w₀ ((x <• g : S3) : EuclideanSpace ℝ (Fin 4)))) =
    (hopf x, phase (w₀ x) * g)
  rw [hopf_smul, w₀_smul, phase_mul_circle hx]

lemma triv₁_smul (x : S3) (hx : w₁ x ≠ 0) (g : Circle) :
    triv₁ (x <• g) = (hopf x, (triv₁ x).2 * g) := by
  change (hopf (x <• g), phase (w₁ ((x <• g : S3) : EuclideanSpace ℝ (Fin 4)))) =
    (hopf x, phase (w₁ x) * g)
  rw [hopf_smul, w₁_smul, phase_mul_circle hx]

/-! ### Freeness of the action -/

lemma eq_one_of_mul_eq {z : ℂ} (hz : z ≠ 0) {g : Circle} (h : z * g = z) : g = 1 := by
  apply Circle.ext
  have : z * ((g : ℂ) - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hz
  · rw [Circle.coe_one]; exact sub_eq_zero.mp h1

lemma w_ne_zero (x : S3) : w₀ x ≠ 0 ∨ w₁ x ≠ 0 := by
  by_contra h
  push_neg at h
  have := S3_norm_sq x
  rw [h.1, h.2] at this
  norm_num at this

lemma stabilizer_eq_bot (x : S3) : MulAction.stabilizer (MulOpposite Circle) x = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [Subgroup.mem_bot]
  have h0 : w₀ x * g.unop = w₀ x := by
    have := congrArg (fun y : S3 => w₀ (y : EuclideanSpace ℝ (Fin 4))) hg
    simpa [coe_smul] using this
  have h1 : w₁ x * g.unop = w₁ x := by
    have := congrArg (fun y : S3 => w₁ (y : EuclideanSpace ℝ (Fin 4))) hg
    simpa [coe_smul] using this
  apply MulOpposite.unop_injective
  rcases w_ne_zero x with hx | hx
  · exact eq_one_of_mul_eq hx h0
  · exact eq_one_of_mul_eq hx h1

/-! ### The local trivialisations, chosen pointwise -/

open Classical in
/-- The local trivialisation used at `p`: over `{w₀ ≠ 0}` if `w₀ p ≠ 0`, else over `{w₁ ≠ 0}`. -/
def localTriv (p : S3) : Trivialization Circle hopf :=
  if w₀ p ≠ 0 then triv₀ else triv₁

/-! ### The goal -/

/-- **The Hopf fibration is a principal circle bundle.** -/
instance instIsPrincipalBundle :
    IsPrincipalBundle (𝓡 2) Circle (𝓡 1) S3 (𝓡 3) hopf where
  is_free := stabilizer_eq_bot
  respects_fibres := hopf_smul
  smooth_proj := contMDiff_hopf
  localTriv := localTriv
  mem_baseSet_localTriv := by
    intro p
    unfold localTriv
    split_ifs with h
    · exact (mem_preimage_baseSet₀ p).mpr h
    · have : w₁ p ≠ 0 := (w_ne_zero p).resolve_left h
      exact (mem_preimage_baseSet₁ p).mpr this
  equivariant_localTriv := by
    intro p q hq g
    unfold localTriv at hq ⊢
    split_ifs with h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at hq
      exact triv₀_smul q ((mem_preimage_baseSet₀ q).mp hq) g
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at hq
      exact triv₁_smul q ((mem_preimage_baseSet₁ q).mp hq) g
  smooth_localTriv := by
    intro p
    unfold localTriv
    split_ifs
    · exact contMDiffOn_triv₀Fun
    · exact contMDiffOn_triv₁Fun

/-- The action is smooth, as needed for fundamental vector fields and connection forms. -/
instance instSmoothRightGAction : SmoothRightGAction ∞ (𝓡 1) (𝓡 3) Circle S3 :=
  ⟨contMDiff_smul_map⟩

end Hopf
