/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineNeighborhoodStability
public import FLT.Mazur.AuxiliaryLevelFiniteType

/-!
# Common affine neighborhoods on finite marking loci

Iterate the relative-product construction over an affine base, then transport
through the actual marking-power comparison. Closed multiplication equations
and the faithful open retain common affine neighborhoods for all finite sets.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The constructed iterated relative product retains common affine neighborhoods. -/
theorem finProperProduct (S : Scheme) [IsAffine S] :
    ∀ (n : ℕ) (Y : Fin n → Scheme) (p : ∀ i, Y i ⟶ S)
      (hp : ∀ i, IsProper (p i)), (∀ i, HasNeighborhoods (Y i)) →
        HasNeighborhoods (Chow.finProperProduct S n Y p hp).obj
  | 0, _, _, _, _ => of_affine S
  | n + 1, Y, p, hp, hY =>
    pullback (p 0) (Chow.finProperProduct S n (fun i => Y i.succ)
      (fun i => p i.succ) (fun i => hp i.succ)).base (hY 0)
      (finProperProduct S n _ _ _ (fun i => hY i.succ))

variable {S : Scheme} [IsAffine S] (E : Over S) [GrpObj E] [IsProper E.hom]
  (A : Type) [Group A] [Fintype A] (hE : HasNeighborhoods E.left)

omit [GrpObj E] [Group A] [Fintype A] in
include hE in
/-- The original categorical marking power has common affine neighborhoods. -/
theorem markingPower [Finite A] : HasNeighborhoods (∏ᶜ fun _ : A => E).left := by
  let _ := Fintype.ofFinite A
  exact of_affineHom (AuxiliaryLevel.markingPowerProperIso E A).hom.left
    (finProperProduct S (Fintype.card A) _ _ _ (fun _ => hE))

include hE in
/-- The closed marking equations retain all finite affine neighborhoods. -/
theorem homScheme : HasNeighborhoods (AuxiliaryLevel.homScheme E A).left :=
  of_affineHom (AuxiliaryLevel.homInclusion E A).left (markingPower E A hE)

include hE in
/-- Removing nonfaithful markings still gives common affine neighborhoods. -/
theorem faithfulScheme : HasNeighborhoods (AuxiliaryLevel.faithfulScheme E A).left :=
  of_openImmersion (AuxiliaryLevel.faithfulInclusion E A).left (homScheme E A hE)

end FLT.Mazur.FiniteAffineNeighborhood
