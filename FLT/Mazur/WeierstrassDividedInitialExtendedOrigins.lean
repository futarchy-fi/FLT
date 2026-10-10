/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExtendedSections

/-!
# Ordered origins in the full extended initial nodes

Both initial extended global sections factor through their corresponding full
node. Projection retains the original origin and its original tangent ordering.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "p" => globalResidueExtensionMap hπ data S j hj
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "first" => initialExtendedFirstSection hπ data D j hj hstart hk S
local notation "second" => initialExtendedSecondSection hπ data D j hj hstart hk S
local notation "N₁" => initialGlobalResidueFirstNode hπ data D j hj hstart hk
local notation "N₂" => initialGlobalResidueSecondNode hπ data D j hj hstart hk
local notation "o₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (fullNodeOrigin a c ha)))
local notation "o₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (fullNodeOrigin (-a) c (IsUnit.neg ha))))

/-- The first original origin lifts into the entire extended first node. -/
def initialExtendedFirstNodeOrigin : Spec (.of S) ⟶ pullback p N₁ :=
  pullback.lift first (e ≫ o₁) (by
    rw [initialExtendedFirstSection_projection, Category.assoc, initialGlobalFirstNode_origin])

/-- The opposite original origin lifts into the entire extended second node. -/
def initialExtendedSecondNodeOrigin : Spec (.of S) ⟶ pullback p N₂ :=
  pullback.lift second (e ≫ o₂) (by
    rw [initialExtendedSecondSection_projection, Category.assoc,
      initialGlobalSecondNode_origin])

/-- The entire first node sends its origin to the first extended global section. -/
@[reassoc] theorem initialExtendedFirstNodeOrigin_global :
    initialExtendedFirstNodeOrigin hπ data D j hj hstart hk S ≫ pullback.fst p N₁ =
      first := pullback.lift_fst _ _ _

/-- The entire second node sends its origin to the opposite extended global section. -/
@[reassoc] theorem initialExtendedSecondNodeOrigin_global :
    initialExtendedSecondNodeOrigin hπ data D j hj hstart hk S ≫ pullback.fst p N₂ =
      second := pullback.lift_fst _ _ _

/-- The first extended origin projects to the original ordered full-node origin. -/
@[reassoc] theorem initialExtendedFirstNodeOrigin_original :
    initialExtendedFirstNodeOrigin hπ data D j hj hstart hk S ≫ pullback.snd p N₁ =
      e ≫ o₁ := pullback.lift_snd _ _ _

/-- The second extended origin projects to the original opposite full-node origin. -/
@[reassoc] theorem initialExtendedSecondNodeOrigin_original :
    initialExtendedSecondNodeOrigin hπ data D j hj hstart hk S ≫ pullback.snd p N₂ =
      e ≫ o₂ := pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
