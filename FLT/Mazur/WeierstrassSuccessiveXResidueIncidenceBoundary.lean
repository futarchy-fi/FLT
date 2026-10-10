/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueIncidencePoints
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PrincipalOpenVanishingIntersection

/-!
# Both ordered incidence points miss the original transition boundaries

Vanishing of the original tensor boundary functions proves that the entire
scheme intersection with either node section is empty.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "first" => residueFirstIncidencePoint D k hk0 hk b3 b4 b6 h3 h4
local notation "second" => residueSecondIncidencePoint D k hk0 hk b3 b4 b6 h3 h4

/-- Every original principal coordinate boundary excludes the zero-slope node section. -/
theorem residueFirstIncidenceBoundary_isPullback (i : Fin 3) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion K (coord W (π ^ k) π b3 b4 b6 i))
      (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom first))) :=
  PrincipalOpenVanishingIntersection.isPullback (AlgHom.toRingHom first)
    (tensorCoord W (π ^ k) π b3 b4 b6 K i)
    (residueFirstIncidencePoint_coord D k hk0 hk b3 b4 b6 h3 h4 i)

/-- Both transition boundaries exclude the opposite node; its tangent coordinate is retained. -/
theorem residueSecondIncidenceBoundary_isPullback (i : Fin 3) (hi : i ≠ 1) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (PrincipalOpenTensor.inclusion K (coord W (π ^ k) π b3 b4 b6 i))
      (Spec.map (CommRingCat.ofHom (AlgHom.toRingHom second))) := by
  apply PrincipalOpenVanishingIntersection.isPullback (AlgHom.toRingHom second)
    (tensorCoord W (π ^ k) π b3 b4 b6 K i)
  change second (tensorCoord W (π ^ k) π b3 b4 b6 K i) = 0
  rw [residueSecondIncidencePoint_coord]
  fin_cases i
  · rfl
  · exact False.elim (hi rfl)
  · rfl

end FLT.Mazur.WeierstrassSuccessiveX
