/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroConicBoundary
public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceOrientation
public import FLT.Mazur.PrincipalOpenVanishingIntersection

/-!
# The initial ordered nodes miss the full tensor incidence boundary

Both maps are the original ordered horizontal-fiber sections transported by
the scale-one normalization. Their entire boundary intersections are empty.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
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
local notation "ha" => D.a₁_unit.map (residue R)
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "E" => zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "t" => coord W (π ^ k) π b3 b4 b6 0

/-- The original first ordered section as a map from the entire tensor algebra. -/
def zeroFirstIncidenceMap : T →ₐ[K] K :=
  (fullFirstIncidencePoint a c ha).comp (E).toAlgHom

/-- The original second ordered section retains its opposite tangent orientation. -/
def zeroSecondIncidenceMap : T →ₐ[K] K :=
  (fullSecondIncidencePoint a c ha).comp (E).toAlgHom

/-- The entire first node section misses the original tensor incidence open. -/
theorem zeroFirstIncidenceBoundary_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion K t)
      (Spec.map (CommRingCat.ofHom
        (zeroFirstIncidenceMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom)) := by
  apply PrincipalOpenVanishingIntersection.isPullback _
    (tensorCoord W (π ^ k) π b3 b4 b6 K 0)
  change fullFirstIncidencePoint a c ha (E (tensorCoord W (π ^ k) π b3 b4 b6 K 0)) = 0
  rw [zeroResidueFiberEquiv_t, fullFirstIncidencePoint_t]

/-- The entire opposite node section misses that same full incidence open. -/
theorem zeroSecondIncidenceBoundary_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion K t)
      (Spec.map (CommRingCat.ofHom
        (zeroSecondIncidenceMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom)) := by
  apply PrincipalOpenVanishingIntersection.isPullback _
    (tensorCoord W (π ^ k) π b3 b4 b6 K 0)
  change fullSecondIncidencePoint a c ha (E (tensorCoord W (π ^ k) π b3 b4 b6 K 0)) = 0
  rw [zeroResidueFiberEquiv_t, fullSecondIncidencePoint_t]

end FLT.Mazur.WeierstrassSuccessiveX
