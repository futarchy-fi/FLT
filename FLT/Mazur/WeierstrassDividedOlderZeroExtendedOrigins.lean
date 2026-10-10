/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderZeroExtendedSections

/-!
# Ordered origins in the entire extended nodes and conic

Each ordered section factors through its full node and the full conic after
coefficient extension. Both coordinates of these factorizations are the actual
extended global section and the original ordered origin. The pullbacks retain
all branches, including when the divided conic constant vanishes.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "first" => olderZeroExtendedFirstSection hπ data D j hj r hr hk0 hk S
local notation "second" => olderZeroExtendedSecondSection hπ data D j hj r hr hk0 hk S
local notation "N₁" => olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk
local notation "N₂" => olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk
local notation "C" => olderGlobalZeroConic hπ data D j hj r hr hk0 hk
local notation "o₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (fullNodeOrigin a c ha)))
local notation "o₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (fullNodeOrigin (-a) c (IsUnit.neg ha))))
local notation "t₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicFirstIncidencePoint a c ha)))
local notation "t₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicSecondIncidencePoint a c ha)))

/-- The first original origin lifts into the entire extended first node. -/
def olderZeroExtendedFirstNodeOrigin : Spec (.of S) ⟶ pullback p N₁ :=
  pullback.lift first (e ≫ o₁) (by
    rw [olderZeroExtendedFirstSection_projection, Category.assoc, olderGlobalZeroFirstNode_origin])

/-- The opposite original origin lifts into the entire extended second node. -/
def olderZeroExtendedSecondNodeOrigin : Spec (.of S) ⟶ pullback p N₂ :=
  pullback.lift second (e ≫ o₂) (by
    rw [olderZeroExtendedSecondSection_projection, Category.assoc,
      olderGlobalZeroSecondNode_origin])

/-- The entire first node sends its origin to the first extended global section. -/
@[reassoc] theorem olderZeroExtendedFirstNodeOrigin_global :
    olderZeroExtendedFirstNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p N₁ =
      first := pullback.lift_fst _ _ _

/-- The entire second node sends its origin to the opposite extended global section. -/
@[reassoc] theorem olderZeroExtendedSecondNodeOrigin_global :
    olderZeroExtendedSecondNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p N₂ =
      second := pullback.lift_fst _ _ _

/-- The first extended origin projects to the original ordered full-node origin. -/
@[reassoc] theorem olderZeroExtendedFirstNodeOrigin_original :
    olderZeroExtendedFirstNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p N₁ =
      e ≫ o₁ := pullback.lift_snd _ _ _

/-- The second extended origin projects to the original opposite full-node origin. -/
@[reassoc] theorem olderZeroExtendedSecondNodeOrigin_original :
    olderZeroExtendedSecondNodeOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p N₂ =
      e ≫ o₂ := pullback.lift_snd _ _ _

/-- The first ordered conic incidence point lifts into the full extended conic. -/
def olderZeroExtendedFirstConicPoint : Spec (.of S) ⟶ pullback p C :=
  pullback.lift first (e ≫ t₁) (by
    rw [olderZeroExtendedFirstSection_projection, Category.assoc,
      olderGlobalZeroFirstSection_conic])

/-- The second ordered conic incidence point lifts into that same full extended conic. -/
def olderZeroExtendedSecondConicPoint : Spec (.of S) ⟶ pullback p C :=
  pullback.lift second (e ≫ t₂) (by
    rw [olderZeroExtendedSecondSection_projection, Category.assoc,
      olderGlobalZeroSecondSection_conic])

/-- The full conic sends its first incidence point to the first ordered global section. -/
@[reassoc] theorem olderZeroExtendedFirstConicPoint_global :
    olderZeroExtendedFirstConicPoint hπ data D j hj r hr hk0 hk S ≫ pullback.fst p C =
      first := pullback.lift_fst _ _ _

/-- The full conic sends its second incidence point to the second ordered global section. -/
@[reassoc] theorem olderZeroExtendedSecondConicPoint_global :
    olderZeroExtendedSecondConicPoint hπ data D j hj r hr hk0 hk S ≫ pullback.fst p C =
      second := pullback.lift_fst _ _ _

/-- The first conic point keeps the exact original ordered incidence point. -/
@[reassoc] theorem olderZeroExtendedFirstConicPoint_original :
    olderZeroExtendedFirstConicPoint hπ data D j hj r hr hk0 hk S ≫ pullback.snd p C =
      e ≫ t₁ := pullback.lift_snd _ _ _

/-- The second conic point keeps the exact original opposite incidence point. -/
@[reassoc] theorem olderZeroExtendedSecondConicPoint_original :
    olderZeroExtendedSecondConicPoint hπ data D j hj r hr hk0 hk S ≫ pullback.snd p C =
      e ≫ t₂ := pullback.lift_snd _ _ _

/-- The ordered conic incidence points remain distinct after every nonzero extension. -/
theorem olderZeroExtendedConicPoints_ne [Nontrivial S] :
    olderZeroExtendedFirstConicPoint hπ data D j hj r hr hk0 hk S ≠
      olderZeroExtendedSecondConicPoint hπ data D j hj r hr hk0 hk S := by
  intro h
  have h' := congrArg (fun t => t ≫ pullback.fst p C) h
  rw [olderZeroExtendedFirstConicPoint_global, olderZeroExtendedSecondConicPoint_global] at h'
  exact olderZeroExtendedSections_ne hπ data D j hj r hr hk0 hk S h'

end FLT.Mazur.WeierstrassDividedDepth
