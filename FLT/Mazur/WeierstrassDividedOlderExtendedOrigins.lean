/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSections

/-!
# Ordered origins in the entire extended middle nodes

Both actual extended global sections factor through their corresponding full
middle node. The projection retains the original origin and tangent ordering.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "first" => olderExtendedFirstSection hπ data D j hj r hr hk0 hk S
local notation "second" => olderExtendedSecondSection hπ data D j hj r hr hk0 hk S
local notation "N₁" => olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk
local notation "N₂" => olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk
local notation "o" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (middleNodeOrigin c)))

/-- The first original origin lifts into the entire extended first node. -/
def olderExtendedFirstNodeOrigin : Spec (.of S) ⟶ pullback p N₁ :=
  pullback.lift first (e ≫ o) (by
    rw [olderExtendedFirstSection_projection, Category.assoc, olderGlobalFirstNode_origin])

/-- The opposite original origin lifts into the entire extended second node. -/
def olderExtendedSecondNodeOrigin : Spec (.of S) ⟶ pullback p N₂ :=
  pullback.lift second (e ≫ o) (by
    rw [olderExtendedSecondSection_projection, Category.assoc,
      olderGlobalSecondNode_origin])

/-- The entire first node sends its origin to the first extended global section. -/
@[reassoc] theorem olderExtendedFirstNodeOrigin_global :
    olderExtendedFirstNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p N₁ =
      first := pullback.lift_fst _ _ _

/-- The entire second node sends its origin to the opposite extended global section. -/
@[reassoc] theorem olderExtendedSecondNodeOrigin_global :
    olderExtendedSecondNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p N₂ =
      second := pullback.lift_fst _ _ _

/-- The first extended origin projects to the original ordered full-node origin. -/
@[reassoc] theorem olderExtendedFirstNodeOrigin_original :
    olderExtendedFirstNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p N₁ =
      e ≫ o := pullback.lift_snd _ _ _

/-- The second extended origin projects to the original opposite full-node origin. -/
@[reassoc] theorem olderExtendedSecondNodeOrigin_original :
    olderExtendedSecondNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p N₂ =
      e ≫ o := pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
