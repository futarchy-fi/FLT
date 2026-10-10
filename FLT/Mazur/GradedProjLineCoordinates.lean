/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Equal-degree coordinates on a graded projective spectrum

Homogeneous elements of the same positive degree give chart ratios and
invertible transition coefficients. No polynomial presentation is required.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.GradedProjLine

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type u} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The chart of a chosen homogeneous coordinate. -/
def chart (i : ι) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (f i)

/-- The fraction `f j / f i` on the i-th chart. -/
def coordinate (i j : ι) : Away 𝒜 (f i) :=
  Away.mk 𝒜 (hf i) 1 (f j) (by simpa only [one_smul] using hf j)

@[simp] lemma coordinate_self (i : ι) : coordinate 𝒜 f hf i i = 1 := by
  apply val_injective
  simp only [coordinate, Away.val_mk, val_one, pow_one]
  exact Localization.mk_self ⟨f i, Submonoid.mem_powers _⟩

/-- Restriction of homogeneous fractions to the pairwise overlap. -/
def toOverlap (i j : ι) : Away 𝒜 (f i) →+* Away 𝒜 (f i * f j) :=
  awayMap 𝒜 (hf j) rfl

/-- On an overlap the coordinate ratio has numerator `f j * f j`. -/
lemma toOverlap_coordinate (i j : ι) :
    toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i j) =
      Away.mk 𝒜 (SetLike.mul_mem_graded (hf i) (hf j)) 1
        (f j * f j) (by simpa only [one_smul] using
          SetLike.mul_mem_graded (hf j) (hf j)) := by
  dsimp only [toOverlap, coordinate]
  simpa only [pow_one] using
    (awayMap_mk 𝒜 (hf j) (f := f i) rfl 1 (hf i) (f j) (by simpa only [one_smul] using hf j))

/-- The coordinate ratio is invertible on the overlap, with reciprocal `f i / f j`. -/
lemma isUnit_ratio (i j : ι) :
    IsUnit (toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i j)) := by
  apply IsUnit.of_mul_eq_one
    (Away.mk 𝒜 (SetLike.mul_mem_graded (hf i) (hf j)) 1 (f i * f i)
      (by simpa only [one_smul] using SetLike.mul_mem_graded (hf i) (hf i)))
  rw [toOverlap_coordinate]
  apply val_injective
  simp only [val_mul, val_one, Away.val_mk, pow_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The transition unit with basis convention `e i = f i`. -/
def ratioUnit (i j : ι) : (Away 𝒜 (f i * f j))ˣ :=
  (isUnit_ratio 𝒜 f hf i j).unit

@[simp] lemma ratioUnit_val (i j : ι) :
    (ratioUnit 𝒜 f hf i j : Away 𝒜 (f i * f j)) =
      toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i j) :=
  (isUnit_ratio 𝒜 f hf i j).unit_spec

@[simp] lemma ratioUnit_self (i : ι) : ratioUnit 𝒜 f hf i i = 1 := by
  apply Units.ext
  simp only [ratioUnit_val, coordinate_self, map_one, Units.val_one]

end FLT.Mazur.GradedProjLine
