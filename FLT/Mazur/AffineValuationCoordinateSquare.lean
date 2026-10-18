/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineValuationGeneratorLift

/-!
# Affine valuative squares from actual coordinate maps

Construct a scheme square from compatible scalar and generic coordinate maps.
The construction retains the coordinates and the exact original center, so
an algebraic pole obstructs a geometric lift of this same square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AffineValuationGeneratorLift
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Field K] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (V : ValuationSubring K)
  (f : R →+* V) (g : Γ(X, ⊤) →+* K)
  (h : g.comp s = V.subtype.comp f)

/-- The affine square defined by the full original scalar and generic coordinate maps. -/
def squareOfCoordinates : ValuativeCommSq (scalarMorphism s) where
  R := V
  K := K
  i₁ := Spec.map (CommRingCat.ofHom g) ≫ inv X.toSpecΓ
  i₂ := Spec.map (CommRingCat.ofHom f)
  commSq := ⟨by
    dsimp only [scalarMorphism]
    rw [Category.assoc, IsIso.inv_hom_id_assoc, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun a : R →+* K ↦ Spec.map (CommRingCat.ofHom a)) h⟩

/-- The generic coordinates of the constructed square are exactly the supplied map. -/
theorem squareOfCoordinates_generic :
    genericCoordinates s (squareOfCoordinates s V f g h) = g := by
  unfold genericCoordinates squareOfCoordinates
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Spec.preimage_map]
  rfl

/-- The center coordinates are exactly the supplied scalar map. -/
theorem squareOfCoordinates_center :
    centerCoordinates s (squareOfCoordinates s V f g h) = f := by
  unfold centerCoordinates squareOfCoordinates
  rw [Spec.preimage_map]
  rfl

/-- The geometric center contracts to the same original scalar ideal. -/
theorem squareOfCoordinates_center_ideal :
    ((squareOfCoordinates s V f g h).i₂ (closedPoint V)).asIdeal =
      (maximalIdeal V).comap f := rfl

/-- A coordinate outside the valuation ring obstructs a lift of the constructed scheme square. -/
theorem squareOfCoordinates_not_hasLift (b : Γ(X, ⊤)) (hb : g b ∉ V) :
    ¬ (squareOfCoordinates s V f g h).commSq.HasLift := by
  intro hl
  obtain ⟨l⟩ := (CommSq.HasLift.iff _).mp hl
  have he := congrArg (fun a : Γ(X, ⊤) →+* K ↦ a b)
    (coordinates_of_lift s (squareOfCoordinates s V f g h) l)
  rw [squareOfCoordinates_generic] at he
  apply hb
  rw [he]
  exact ((Spec.preimage (l.l ≫ X.toSpecΓ)).hom b).property

end FLT.Mazur.AffineValuationGeneratorLift
