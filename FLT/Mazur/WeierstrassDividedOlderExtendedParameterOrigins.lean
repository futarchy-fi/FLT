/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSections
public import FLT.Mazur.WeierstrassDividedOlderGlobalParameterSections

/-!
# Ordered origins in the extended conic parameter charts

Each actual extended global section lifts to its full rational parameter
chart, and projection recovers the original parameter origin.
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
local notation "P₁" => olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk
local notation "P₂" => olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))

/-- The first section lifts into its entire extended parameter chart. -/
def olderExtendedFirstParameterOrigin : Spec (.of S) ⟶ pullback p P₁ :=
  pullback.lift first (e ≫ o) (by
    rw [olderExtendedFirstSection_projection, Category.assoc,
      olderGlobalFirstSection_parameter])

/-- The full parameter chart sends its origin to the first extended section. -/
@[reassoc] theorem olderExtendedFirstParameterOrigin_global :
    olderExtendedFirstParameterOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p P₁ =
      first := pullback.lift_fst _ _ _

/-- The first extended origin projects to the original rational parameter origin. -/
@[reassoc] theorem olderExtendedFirstParameterOrigin_original :
    olderExtendedFirstParameterOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p P₁ =
      e ≫ o := pullback.lift_snd _ _ _

/-- The second section lifts into its entire extended parameter chart. -/
def olderExtendedSecondParameterOrigin : Spec (.of S) ⟶ pullback p P₂ :=
  pullback.lift second (e ≫ o) (by
    rw [olderExtendedSecondSection_projection, Category.assoc,
      olderGlobalSecondSection_parameter])

/-- The full parameter chart sends its origin to the second extended section. -/
@[reassoc] theorem olderExtendedSecondParameterOrigin_global :
    olderExtendedSecondParameterOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.fst p P₂ =
      second := pullback.lift_fst _ _ _

/-- The second extended origin projects to the original rational parameter origin. -/
@[reassoc] theorem olderExtendedSecondParameterOrigin_original :
    olderExtendedSecondParameterOrigin hπ data D j hj r hr hk0 hk S ≫ pullback.snd p P₂ =
      e ≫ o := pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
