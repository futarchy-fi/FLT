/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenVanishingIntersection
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# The residue components avoid their opposite transition boundaries

Every horizontal line misses the full next-depth boundary. The conic misses
the full preceding horizontal boundary. Both are empty scheme intersections.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "E" => residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4
local notation "C" => residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "u" => coord W (π ^ k) π b3 b4 b6 2

/-- Any retained horizontal line misses the entire next-depth incidence open. -/
theorem residueLineBoundary_isPullback (r : K) (hr : r * (r + a) = 0) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo (Spec (.of (Polynomial K))))
      (PrincipalOpenTensor.inclusion K t)
      (residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr) := by
  rw [residueSuccessiveLineImmersion_eq_spec]
  exact PrincipalOpenVanishingIntersection.isPullback
    (residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr).toRingHom
    (tensorCoord W (π ^ k) π b3 b4 b6 K 0)
    (residueSuccessiveLineMap_coord D k hk0 hk b3 b4 b6 h3 h4 r hr 0)

/-- No point of a retained horizontal line lies in the next-depth incidence open. -/
theorem residueLineBoundary_disjoint (r : K) (hr : r * (r + a) = 0) :
    Disjoint (Set.range (PrincipalOpenTensor.inclusion K t))
      (Set.range (residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr)) := by
  rw [residueSuccessiveLineImmersion_eq_spec]
  exact PrincipalOpenVanishingIntersection.disjoint
    (residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr).toRingHom
    (tensorCoord W (π ^ k) π b3 b4 b6 K 0)
    (residueSuccessiveLineMap_coord D k hk0 hk b3 b4 b6 h3 h4 r hr 0)

/-- The full conic has empty intersection with the preceding horizontal boundary. -/
theorem residueConicHorizontal_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (PrincipalOpenTensor.inclusion K u) C := by
  rw [residueSuccessiveConicImmersion_eq_spec]
  exact PrincipalOpenVanishingIntersection.isPullback
    (residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom
    (tensorCoord W (π ^ k) π b3 b4 b6 K 2)
    (residueSuccessiveConicMap_coord D k hk0 hk b3 b4 b6 h3 h4 2)

end FLT.Mazur.WeierstrassSuccessiveX
