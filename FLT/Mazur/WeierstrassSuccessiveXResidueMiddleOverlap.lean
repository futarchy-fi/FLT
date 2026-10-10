/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransport
public import FLT.Mazur.WeierstrassSuccessiveXMiddleOverlap
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleContraction

/-!
# The actual tensor middle overlap and its contraction

Localizing the original tensor incidence coordinate gives the original conic
incidence open. The comparison commutes with restriction of every tensor
function and sends both coordinates of the preceding contraction to zero.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "e" => residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The actual incidence open in the tensor residue chart. -/
abbrev ResidueMiddleOpen := Localization.Away (tensorCoord W (π ^ k) π b3 b4 b6 K 0)

/-- Residue normalization retains the entire principal localization. -/
def residueMiddleOpenEquiv : ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K]
    XOpen W₀ 0 0 0 0 c :=
  PrincipalOpenTransport.equiv e _ _
    (residueRetainedFiberEquiv_coord D k hk0 hk b3 b4 b6 h3 h4 0)

/-- The whole original tensor incidence open is the actual conic incidence open. -/
def residueMiddleConicOpenEquiv :
    ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleConicOpen W₀ c :=
  (residueMiddleOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
    (middleOverlapConicEquiv W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem))

/-- The tensor-to-conic open square commutes on every original function. -/
@[simp] theorem residueMiddleConicOpenEquiv_base (z : T) :
    residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4 (algebraMap T _ z) =
      algebraMap C₀ (MiddleConicOpen W₀ c)
        (residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4 z) := by
  change middleOverlapToConic W₀ c _
    (PrincipalOpenTransport.equiv e _ _
      (residueRetainedFiberEquiv_coord D k hk0 hk b3 b4 b6 h3 h4 0)
      (algebraMap T _ z)) = _
  rw [PrincipalOpenTransport.equiv_base, middleOverlapToConic_base]
  rfl

include D hk0 hk h3 h4 in
/-- The actual preceding horizontal contraction vanishes on the complete overlap. -/
theorem residueMiddleOpen_previous_x :
    algebraMap T (ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6)
      (tensorPreviousMap W (π ^ k) π b3 b4 b6 K
        (WeierstrassDilatation.x W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6))) = 0 := by
  apply (residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).injective
  rw [residueMiddleConicOpenEquiv_base, residueSuccessiveConic_previous_x, map_zero,
    map_zero]

include D hk0 hk h3 h4 in
/-- The preceding vertical contraction vanishes on that same actual overlap. -/
theorem residueMiddleOpen_previous_y :
    algebraMap T (ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6)
      (tensorPreviousMap W (π ^ k) π b3 b4 b6 K
        (WeierstrassDilatation.y W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6))) = 0 := by
  apply (residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).injective
  rw [residueMiddleConicOpenEquiv_base, residueSuccessiveConic_previous_y, map_zero,
    map_zero]

end FLT.Mazur.WeierstrassSuccessiveX
