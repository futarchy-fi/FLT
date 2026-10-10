/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleContraction
public import FLT.Mazur.WeierstrassSuccessiveXMiddleExtension
public import FLT.Mazur.WeierstrassSuccessiveXMiddleUnion

/-!
# The full scheme structure of the actual successive middle residue fiber

The original tensor fiber is the retained conic with the incidence variable
adjoined. Its conic and two ordered lines jointly detect every function.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "e" => residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The entire actual tensor residue fiber is the retained conic extension, without reduction. -/
def residueMiddleExtensionEquiv : T ≃ₐ[K] MiddleExtension W₀ (residue R b6) :=
  (e).trans (middleExtensionEquiv W₀ (residue R b6) ((residue_eq_zero_iff _).mpr D.a₂_mem))

/-- The actual conic and both original horizontal lines detect every tensor-fiber function. -/
theorem residue_middle_components_detect_zero (z : T)
    (hc : residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4 z = 0)
    (h0 : residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4
      0 (middle_first_root W₀) z = 0)
    (h1 : residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4
      (-residue R W.a₁) (middle_second_root W₀) z = 0) : z = 0 := by
  apply (e).injective
  rw [map_zero]
  exact middle_components_detect_zero W₀ (residue R b6)
    ((residue_eq_zero_iff _).mpr D.a₂_mem) (D.a₁_unit.map (residue R)) (e z) hc h0 h1

end FLT.Mazur.WeierstrassSuccessiveX
