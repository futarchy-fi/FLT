/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonPinchingAlgebra

/-!
# Descent from the pinched affine line to affine targets

The ring pullback supplies unique scheme morphisms to affine targets.
This does not assert descent to arbitrary schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.PolygonNodePresentation
open FLT.Mazur.OneGonPinchingAlgebra

namespace FLT.Mazur.OneGonAffineDescent

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Compatible maps from the affine line and the identified point descend
uniquely when the target is an affine spectrum. -/
theorem existsUnique_desc_spec
    (f : Spec (.of (Polynomial R)) ⟶ Spec (.of S))
    (g : Spec (.of R) ⟶ Spec (.of S))
    (h : Spec.map (CommRingCat.ofHom endpoints) ≫ f =
      Spec.map (CommRingCat.ofHom diagonal) ≫ g) :
    ∃! d : Spec (.of (B (R := R))) ⟶ Spec (.of S),
      toPinching ≫ d = f ∧
        Spec.map (CommRingCat.ofHom bEval.toRingHom) ≫ d = g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have hc : endpoints.comp φ.hom = diagonal.comp ψ.hom :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨Spec.map (CommRingCat.ofHom (lift φ.hom ψ.hom hc)), ⟨?_, ?_⟩, ?_⟩
  · rw [toPinching, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact inclusion_lift φ.hom ψ.hom hc
  · rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact evaluation_lift φ.hom ψ.hom hc
  · rintro d ⟨hd, _⟩
    obtain ⟨δ, rfl⟩ := Spec.map_surjective d
    rw [toPinching, ← Spec.map_comp] at hd
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact lift_unique φ.hom ψ.hom hc δ.hom
      (congrArg CommRingCat.Hom.hom (Spec.map_injective hd))

/-- Descent to any affine scheme, independently of its chosen presentation. -/
theorem existsUnique_desc {X : Scheme.{u}} [IsAffine X]
    (f : Spec (.of (Polynomial R)) ⟶ X) (g : Spec (.of R) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom endpoints) ≫ f =
      Spec.map (CommRingCat.ofHom diagonal) ≫ g) :
    ∃! d : Spec (.of (B (R := R))) ⟶ X,
      toPinching ≫ d = f ∧
        Spec.map (CommRingCat.ofHom bEval.toRingHom) ≫ d = g := by
  obtain ⟨d, hd, hu⟩ := existsUnique_desc_spec
    (f ≫ X.isoSpec.hom) (g ≫ X.isoSpec.hom)
    (by simpa only [Category.assoc] using
      congrArg (fun m ↦ m ≫ X.isoSpec.hom) h)
  refine ⟨d ≫ X.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun m ↦ m ≫ X.isoSpec.inv) hd.1
  · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun m ↦ m ≫ X.isoSpec.inv) hd.2
  · rintro e ⟨he₁, he₂⟩
    have he : e ≫ X.isoSpec.hom = d := hu _ ⟨
      by simpa only [Category.assoc] using
        congrArg (fun m ↦ m ≫ X.isoSpec.hom) he₁,
      by simpa only [Category.assoc] using
        congrArg (fun m ↦ m ≫ X.isoSpec.hom) he₂⟩
    calc
      e = (e ≫ X.isoSpec.hom) ≫ X.isoSpec.inv := by simp
      _ = d ≫ X.isoSpec.inv := congrArg (fun m ↦ m ≫ X.isoSpec.inv) he

end FLT.Mazur.OneGonAffineDescent
