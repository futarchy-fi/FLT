/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSections
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections

/-!
# Ordered markings in the entire extended middle components

The actual extended sections factor through the full conic and their ordered
horizontal lines. Both projections retain the original incidence markings.
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
open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "L₁" => olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk
local notation "L₂" => olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk
local notation "o₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicFirstIncidencePoint a c ha)))
local notation "o₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicSecondIncidencePoint a c ha)))
local notation "z" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (Polynomial.aeval (0 : K))))

/-- The first section lifts into its full extended conic. -/
def olderExtendedFirstConicOrigin : Spec (.of S) ⟶ pullback p C :=
  pullback.lift first (e ≫ o₁) (by
    rw [olderExtendedFirstSection_projection, Category.assoc,
      olderGlobalFirstSection_conic])

/-- The full extended conic maps its first marking to the ordered section. -/
@[reassoc] theorem olderExtendedFirstConicOrigin_global :
    olderExtendedFirstConicOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p C =
      first := pullback.lift_fst _ _ _

/-- Projection preserves the original first conic marking. -/
@[reassoc] theorem olderExtendedFirstConicOrigin_original :
    olderExtendedFirstConicOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p C =
      e ≫ o₁ := pullback.lift_snd _ _ _

/-- The second section lifts into its full extended conic. -/
def olderExtendedSecondConicOrigin : Spec (.of S) ⟶ pullback p C :=
  pullback.lift second (e ≫ o₂) (by
    rw [olderExtendedSecondSection_projection, Category.assoc,
      olderGlobalSecondSection_conic])

/-- The full extended conic maps its second marking to the ordered section. -/
@[reassoc] theorem olderExtendedSecondConicOrigin_global :
    olderExtendedSecondConicOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p C =
      second := pullback.lift_fst _ _ _

/-- Projection preserves the original second conic marking. -/
@[reassoc] theorem olderExtendedSecondConicOrigin_original :
    olderExtendedSecondConicOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p C =
      e ≫ o₂ := pullback.lift_snd _ _ _

/-- The first section lifts into its full extended line. -/
def olderExtendedFirstLineOrigin : Spec (.of S) ⟶ pullback p L₁ :=
  pullback.lift first (e ≫ z) (by
    rw [olderExtendedFirstSection_projection, Category.assoc,
      olderGlobalFirstSection_line])

/-- The full extended line maps its first marking to the ordered section. -/
@[reassoc] theorem olderExtendedFirstLineOrigin_global :
    olderExtendedFirstLineOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p L₁ =
      first := pullback.lift_fst _ _ _

/-- Projection preserves the original first line marking. -/
@[reassoc] theorem olderExtendedFirstLineOrigin_original :
    olderExtendedFirstLineOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p L₁ =
      e ≫ z := pullback.lift_snd _ _ _

/-- The second section lifts into its full extended line. -/
def olderExtendedSecondLineOrigin : Spec (.of S) ⟶ pullback p L₂ :=
  pullback.lift second (e ≫ z) (by
    rw [olderExtendedSecondSection_projection, Category.assoc,
      olderGlobalSecondSection_line])

/-- The full extended line maps its second marking to the ordered section. -/
@[reassoc] theorem olderExtendedSecondLineOrigin_global :
    olderExtendedSecondLineOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p L₂ =
      second := pullback.lift_fst _ _ _

/-- Projection preserves the original second line marking. -/
@[reassoc] theorem olderExtendedSecondLineOrigin_original :
    olderExtendedSecondLineOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p L₂ =
      e ≫ z := pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
