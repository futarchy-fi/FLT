/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroIncidenceBoundary
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# The entire initial exterior line misses the next incidence boundary

The vanishing original tensor coordinate excludes the full line, including both nodes.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "E" => zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The full exterior affine line as a quotient of the original tensor algebra. -/
def zeroExteriorLineMap : ScalarExtension W (π ^ k) π b3 b4 b6 K →ₐ[K] Polynomial K :=
  (fiberIncidenceMap a c).comp (E).toAlgHom

/-- The whole exterior line has empty intersection with the original incidence open. -/
theorem zeroExteriorLineBoundary_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion K (coord W (π ^ k) π b3 b4 b6 0))
      (Spec.map (CommRingCat.ofHom
        (zeroExteriorLineMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom)) := by
  apply PrincipalOpenVanishingIntersection.isPullback _
    (tensorCoord W (π ^ k) π b3 b4 b6 K 0)
  change fiberIncidenceMap a c (E (tensorCoord W (π ^ k) π b3 b4 b6 K 0)) = 0
  rw [zeroResidueFiberEquiv_t, fiberIncidenceMap_t]

/-- The quotient immersion agrees with the original normalized incidence immersion. -/
theorem zeroExteriorLineMap_spec :
    Spec.map (CommRingCat.ofHom
        (zeroExteriorLineMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) =
      fiberIncidenceImmersion a c ≫
        (zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
