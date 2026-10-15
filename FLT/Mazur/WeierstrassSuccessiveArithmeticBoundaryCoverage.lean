/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchBoundary
public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeCoverage
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The constructed arithmetic Laurent boundaries cover the full original opens

Coverage is transported through the actual tensor equivalence and the exact
branch pullback squares. No original boundary points are discarded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m

/-- Both actual tensor branches cover the whole original successive arithmetic chart. -/
theorem arithmeticTensorBranches_cover (p : Spec (.of (ScalarExtension W s π b3 b4 b6 Q))) :
    ∃ (opposite : Bool), ∃ x,
      arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite x = p := by
  let E := PrimeSpectrum.comapEquiv (baseChangeEquiv W s π b3 b4 b6 Q).toRingEquiv
  obtain ⟨x, hx⟩ | ⟨x, hx⟩ :=
    arithmeticNodeCharts_cover π m W s b3 b4 b6 ha hs h2 h3 h4 h6 (E p)
  · refine ⟨false, x, ?_⟩
    change PrimeSpectrum.comap (baseChangeEquiv W s π b3 b4 b6 Q).toRingHom
      (arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 x) = p
    rw [hx]
    exact E.left_inv p
  · refine ⟨true, x, ?_⟩
    change PrimeSpectrum.comap (baseChangeEquiv W s π b3 b4 b6 Q).toRingHom
      (arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 x) = p
    rw [hx]
    exact E.left_inv p

/-- The two right Laurent branches cover the full original localized tensor boundary. -/
theorem arithmeticRightBoundaries_cover
    (p : Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 Q 2)))) :
    ∃ (opposite : Bool), ∃ x,
      arithmeticBranchRightBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite x = p := by
  obtain ⟨opposite, x, hx⟩ := arithmeticTensorBranches_cover π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 (PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 2) p)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (arithmeticBranchRightBoundary_isPullback π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 opposite) p x hx.symm
  exact ⟨opposite, z, hz⟩

/-- The two left Laurent branches also cover the entire original tensor localization. -/
theorem arithmeticLeftBoundaries_cover
    (p : Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 Q 0)))) :
    ∃ (opposite : Bool), ∃ x,
      arithmeticBranchLeftBoundary π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite x = p := by
  obtain ⟨opposite, x, hx⟩ := arithmeticTensorBranches_cover π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 (PrincipalOpenTensor.inclusion Q (coord W s π b3 b4 b6 0) p)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (arithmeticBranchLeftBoundary_isPullback π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 opposite) p x hx.symm
  exact ⟨opposite, z, hz⟩

end FLT.Mazur.WeierstrassSuccessiveX
