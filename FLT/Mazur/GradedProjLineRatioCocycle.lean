/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineCoordinates

/-!
# Homogeneous transition cocycles

Equal-degree ratios satisfy the multiplicative cocycle on triple overlaps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.GradedProjLine

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type u} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- Homogeneous coordinates on a triple overlap. -/
abbrev tripleRing (i j k : ι) := Away 𝒜 (f i * f j * f k)

/-- Restriction from the first pair to a triple overlap. -/
def toTriple₁₂ (i j k : ι) : Away 𝒜 (f i * f j) →+* tripleRing 𝒜 f i j k :=
  awayMap _ (hf k) rfl

/-- Restriction from the second pair to a triple overlap. -/
def toTriple₂₃ (i j k : ι) : Away 𝒜 (f j * f k) →+* tripleRing 𝒜 f i j k :=
  awayMap _ (hf i) (by ring)

/-- Restriction from the outer pair to a triple overlap. -/
def toTriple₁₃ (i j k : ι) : Away 𝒜 (f i * f k) →+* tripleRing 𝒜 f i j k :=
  awayMap _ (hf j) (by ring)

/-- The coordinate fractions satisfy the cocycle law. -/
lemma ratioUnit_cocycle (i j k : ι) :
    Units.map (toTriple₁₂ 𝒜 f hf i j k).toMonoidHom (ratioUnit 𝒜 f hf i j) *
      Units.map (toTriple₂₃ 𝒜 f hf i j k).toMonoidHom (ratioUnit 𝒜 f hf j k) =
    Units.map (toTriple₁₃ 𝒜 f hf i j k).toMonoidHom (ratioUnit 𝒜 f hf i k) := by
  apply Units.ext
  change toTriple₁₂ 𝒜 f hf i j k (ratioUnit 𝒜 f hf i j) *
    toTriple₂₃ 𝒜 f hf i j k (ratioUnit 𝒜 f hf j k) =
    toTriple₁₃ 𝒜 f hf i j k (ratioUnit 𝒜 f hf i k)
  simp only [ratioUnit_val, toOverlap_coordinate, toTriple₁₂, toTriple₂₃, toTriple₁₃,
    awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk, pow_one, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Integral powers of the coordinate transition. -/
def transitionUnit (n : ℤ) (i j : ι) : (Away 𝒜 (f i * f j))ˣ :=
  ratioUnit 𝒜 f hf i j ^ n

/-- All integer twists satisfy the same overlap cocycle. -/
lemma transitionUnit_cocycle (n : ℤ) (i j k : ι) :
    Units.map (toTriple₁₂ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n i j) *
      Units.map (toTriple₂₃ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n j k) =
    Units.map (toTriple₁₃ 𝒜 f hf i j k).toMonoidHom (transitionUnit 𝒜 f hf n i k) := by
  simp only [transitionUnit, map_zpow, ← mul_zpow, ratioUnit_cocycle]

end FLT.Mazur.GradedProjLine
