/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Affine finite-group quotient schemes

Construct the spectrum of the fixed ring and the invariant integral surjection
onto it. Invariant morphisms to an affine scheme factor uniquely through this
map. The extension to arbitrary scheme targets is a separate gluing theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u

variable (G A : Type u) [Group G] [CommRing A] [MulSemiringAction G A]

/-- The affine quotient scheme, constructed from its invariant coordinate ring. -/
abbrev affineQuotient : Scheme := Spec (.of (invariantRing G A))

/-- The actual quotient morphism is induced by the invariant ring inclusion. -/
def quotientMap : Spec (.of A) ⟶ affineQuotient G A :=
  Spec.map (CommRingCat.ofHom (inclusion G A))

/-- A group element acts on the affine scheme by its coordinate automorphism. -/
def actionMap (g : G) : Spec (.of A) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))

/-- The quotient morphism is invariant under every group element. -/
theorem actionMap_quotientMap (g : G) :
    actionMap G A g ≫ quotientMap G A = quotientMap G A := by
  rw [actionMap, quotientMap, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact smul_inclusion G A g a

/-- The affine quotient map is integral without a freeness hypothesis. -/
instance quotientMap_integral [Finite G] : IsIntegralHom (quotientMap G A) :=
  IsIntegralHom.SpecMap_iff.mpr (inclusion_isIntegral G A)

/-- The actual scheme morphism is surjective on points. -/
instance quotientMap_surjective [Finite G] : Surjective (quotientMap G A) :=
  ⟨spectrum_surjective G A⟩

/-- Coordinate descent gives a unique morphism to any affine spectrum. -/
theorem existsUnique_affine_desc (R : Type u) [CommRing R]
    (f : Spec (.of A) ⟶ Spec (.of R))
    (hf : ∀ g : G, actionMap G A g ≫ f = f) :
    ∃! h : affineQuotient G A ⟶ Spec (.of R), quotientMap G A ≫ h = f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hφ : ∀ (g : G) r, g • φ.hom r = φ.hom r := by
    intro g r
    have h := hf g
    rw [actionMap, ← Spec.map_comp] at h
    exact congrArg (fun k ↦ k.hom r) (Spec.map_injective h)
  refine ⟨Spec.map (CommRingCat.ofHom (lift G A φ.hom hφ)), ?_, ?_⟩
  · dsimp only
    rw [quotientMap, ← Spec.map_comp]
    rfl
  · intro h hh
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective h
    rw [quotientMap, ← Spec.map_comp] at hh
    have he : (inclusion G A).comp ψ.hom = φ.hom :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
    have hψ := (existsUnique_lift G A φ.hom hφ).unique he (inclusion_comp_lift G A φ.hom hφ)
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k)) hψ

end FLT.Mazur.FiniteGroupQuotient
