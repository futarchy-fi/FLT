/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupAffineQuotient
public import FLT.Mazur.FiniteGroupQuotientGeometricPoints

/-!
# Scheme-valued formulation of the affine quotient's geometric points

The actual quotient morphism is surjective on algebraically closed field
points. Two such morphisms have the same image precisely when they differ by
the actual group action. This concerns an arbitrary affine action; the modular
atlas and its boundary must still be constructed before applying it there.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u

variable (G A K : Type u) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  [Field K]

/-- Equality of images under the actual quotient map is the geometric orbit relation. -/
theorem schemePoint_eq_iff_orbit (x y : Spec (.of K) ⟶ Spec (.of A)) :
    x ≫ quotientMap G A = y ≫ quotientMap G A ↔
      ∃ g : G, y = x ≫ actionMap G A g := by
  constructor
  · obtain ⟨φ, rfl⟩ := Spec.map_surjective x
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
    intro h
    rw [quotientMap, ← Spec.map_comp, ← Spec.map_comp] at h
    have he : φ.hom.comp (inclusion G A) = ψ.hom.comp (inclusion G A) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    obtain ⟨g, hg⟩ := exists_ringHom_orbit G A φ.hom ψ.hom he
    refine ⟨g, ?_⟩
    rw [actionMap, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hg
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, actionMap_quotientMap]

/-- Every algebraically closed field-valued scheme point lifts through the quotient morphism. -/
theorem schemePoint_surjective [IsAlgClosed K] :
    Function.Surjective
      (fun x : Spec (.of K) ⟶ Spec (.of A) ↦ x ≫ quotientMap G A) := by
  let _ := Algebra.IsInvariant.isIntegral (invariantRing G A) A G
  intro f
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_integral (invariantRing G A) A φ.hom
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  dsimp only
  rw [quotientMap, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hψ

end FLT.Mazur.FiniteGroupQuotient
