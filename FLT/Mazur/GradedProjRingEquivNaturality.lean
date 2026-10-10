/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjRingEquiv

/-!
# Naturality of the Proj isomorphism from a graded ring equivalence

Composing the actual ring maps before applying Proj keeps large scalar-extension
definitions out of the geometric functoriality calculation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal

universe u

namespace FLT.Mazur.GradedProjRingEquivNaturality

variable {A B C σ τ υ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (e : B ≃+* C) (he : ∀ d b, e b ∈ 𝒞 d ↔ b ∈ ℬ d)
  (f : 𝒜 →+*ᵍ ℬ) (g : 𝒜 →+*ᵍ 𝒞)
  (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ 𝒜₊.map g)

/-- An actual equality of graded maps gives the expected equality of Proj morphisms. -/
@[reassoc]
theorem iso_hom_map (hfg : (GradedProjRingEquiv.forward ℬ 𝒞 e he).comp f = g) :
    (GradedProjRingEquiv.iso ℬ 𝒞 e he).hom ≫ Proj.map f hf = Proj.map g hg := by
  change Proj.map (GradedProjRingEquiv.forward ℬ 𝒞 e he) _ ≫ Proj.map f hf = _
  subst g
  rw [← Proj.map_comp]

end FLT.Mazur.GradedProjRingEquivNaturality
