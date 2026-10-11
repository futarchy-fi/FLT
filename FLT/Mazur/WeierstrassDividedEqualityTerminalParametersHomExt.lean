/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
import all FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters

/-!
# The original terminal parameters and Laurent chart determine projective maps

Both full conic parameter opens and the Laurent chart form the actual cover
of the complete terminal component. No separation condition on the target is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "q₁" => laurentConicComponentFirstParameter D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "q₂" => laurentConicComponentSecondParameter D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
variable {Y : Scheme.{u}} (φ ψ : ProjectiveLine.scheme (ResidueField R) ⟶ Y)

/-- The original two conic parameters and the Laurent chart detect equality. -/
theorem equalityTerminalParameters_hom_ext
    (h₁ : equalityTerminalFirstNodeParameter data D j hj hk hp ≫ φ =
      equalityTerminalFirstNodeParameter data D j hj hk hp ≫ ψ)
    (h₂ : equalityTerminalSecondNodeParameter data D j hj hk hp ≫ φ =
      equalityTerminalSecondNodeParameter data D j hj hk hp ≫ ψ)
    (ht : ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ φ =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ ψ) : φ = ψ := by
  apply (cancel_epi (J).inv).mp
  apply laurentConicComponent_hom_ext
  · apply conicParameter_hom_ext _ _ (D.a₁_unit.map (residue R))
    · simpa only [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter,
        WeierstrassCurve.map_a₁, Category.assoc] using h₁
    · simpa only [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter,
        WeierstrassCurve.map_a₁, Category.assoc] using h₂
  · rw [← laurentConicComponentProjectiveIso_torus D (start + j) hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ht

end FLT.Mazur.WeierstrassDividedDepth
