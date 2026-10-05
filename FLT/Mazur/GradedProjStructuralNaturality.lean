/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjStructuralMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Structural naturality of graded Proj maps

A graded ring map compatible with a map of scalar rings induces a Proj map
commuting with the structural maps. The scalar rings need not coincide.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal
universe u
namespace FLT.Mazur.GradedProjStructuralNaturality
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (ρ : R →+* S)
  (hscalar : ∀ r, φ (algebraMap R A r) = algebraMap S B (ρ r))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
include hscalar

/-- Homogeneous localization carries structural scalars to structural scalars. -/
lemma awayMap_scalar (f : A) (r : R) :
    Away.map φ f (GradedProjStructuralMap.scalarToAway 𝒜 f r) =
      GradedProjStructuralMap.scalarToAway ℬ (φ f) (ρ r) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (φ (algebraMap R A r)) ⟨φ 1, _⟩ =
    Localization.mk (algebraMap S B (ρ r)) ⟨1, _⟩
  simp only [hscalar, map_one]

/-- A graded Proj map respects any compatible structural scalar map. -/
@[reassoc]
lemma map_toSpecBase (hφ : ℬ₊ ≤ 𝒜₊.map φ) :
    Proj.map φ hφ ≫ GradedProjStructuralMap.toSpecBase 𝒜 =
      GradedProjStructuralMap.toSpecBase ℬ ≫ Spec.map (CommRingCat.ofHom ρ) := by
  apply (Proj.mapAffineOpenCover φ hφ).openCover.hom_ext
  intro s
  change Proj.awayι _ _ _ _ ≫ _ = Proj.awayι _ _ _ _ ≫ _
  rw [← Category.assoc, Proj.awayι_comp_map φ hφ s.1.2 s.2 s.2.2,
    Category.assoc, GradedProjStructuralMap.awayι_toSpecBase,
    GradedProjStructuralMap.awayι_toSpecBase_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact awayMap_scalar 𝒜 ℬ φ ρ hscalar s.2 r

end FLT.Mazur.GradedProjStructuralNaturality
