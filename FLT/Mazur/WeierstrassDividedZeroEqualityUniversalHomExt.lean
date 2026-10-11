/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityHomExt
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoHomExt

/-!
# Morphism uniqueness for every start-zero equality cycle

All lengths, including the two-component fiber, are detected by their actual
complete cyclic components. No positivity hypothesis remains on the length.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Every start-zero equality cycle jointly detects arbitrary scheme morphisms. -/
theorem zeroEqualityCycleComponent_hom_ext : f = g := by
  cases s with
  | zero =>
    exact zeroEqualityCycleComponent_hom_ext_lengthTwo hπ data D hs hstart hk hp f g h
  | succ s =>
    exact zeroEqualityCycleComponent_hom_ext_of_pos hπ data D (s + 1) hs
      hstart hk hp (Nat.zero_lt_succ s) f g h

/-- The actual normalization leg is epimorphic at every equality-cycle length. -/
theorem zeroEqualityCycleNormalization_epi :
    Epi (zeroEqualityCycleNormalization hπ data D s hs hstart hk hp) := by
  cases s with
  | zero => exact zeroEqualityCycleNormalization_epi_lengthTwo hπ data D hs hstart hk hp
  | succ s =>
    exact zeroEqualityCycleNormalization_epi_of_pos hπ data D (s + 1) hs
      hstart hk hp (Nat.zero_lt_succ s)

end FLT.Mazur.WeierstrassDividedDepth
