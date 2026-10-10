/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSections
public import FLT.Mazur.WeierstrassDividedOlderGlobalConicOverlap
public import FLT.Mazur.PullbackOverlapBaseChange

/-!
# The actual extended conic parameter overlap

The full double localization after coefficient extension is the intersection
of the two extended rational charts. The comparison keeps both the original
parameter coordinates and the actual extended global coordinate.
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
local notation "O" => olderGlobalConicOverlap hπ data D j hj r hr hk0 hk
local notation "l" => conicOverlapFirstParameterMap a c ha
local notation "r₀" => conicOverlapSecondParameterMap a c ha
local notation "H" => olderGlobalConicOverlap_isPullback hπ data D j hj r hr hk0 hk

/-- The full extended overlap projects to the first extended rational parameter chart. -/
def olderExtendedConicOverlapFirst : pullback p O ⟶ pullback p P₁ :=
  PullbackOverlapBaseChange.first p

/-- The full extended overlap projects to the opposite extended rational parameter chart. -/
def olderExtendedConicOverlapSecond : pullback p O ⟶ pullback p P₂ :=
  PullbackOverlapBaseChange.second H p

/-- The first overlap projection preserves the actual extended global coordinate. -/
@[reassoc] theorem olderExtendedConicOverlapFirst_global :
    olderExtendedConicOverlapFirst hπ data D j hj r hr hk0 hk S ≫ pullback.fst p P₁ =
      pullback.fst p O := PullbackOverlapBaseChange.first_fst p

/-- The second overlap projection preserves the actual extended global coordinate. -/
@[reassoc] theorem olderExtendedConicOverlapSecond_global :
    olderExtendedConicOverlapSecond hπ data D j hj r hr hk0 hk S ≫ pullback.fst p P₂ =
      pullback.fst p O := PullbackOverlapBaseChange.second_fst H p

/-- The first overlap projection retains the original first rational parameter. -/
@[reassoc] theorem olderExtendedConicOverlapFirst_original :
    olderExtendedConicOverlapFirst hπ data D j hj r hr hk0 hk S ≫ pullback.snd p P₁ =
      pullback.snd p O ≫ l := PullbackOverlapBaseChange.first_snd p

/-- The second overlap projection retains the original opposite rational parameter. -/
@[reassoc] theorem olderExtendedConicOverlapSecond_original :
    olderExtendedConicOverlapSecond hπ data D j hj r hr hk0 hk S ≫ pullback.snd p P₂ =
      pullback.snd p O ≫ r₀ := PullbackOverlapBaseChange.second_snd H p

/-- The explicit overlap after extension is the entire intersection of the extended charts. -/
theorem olderExtendedConicOverlap_isPullback :
    IsPullback (olderExtendedConicOverlapFirst hπ data D j hj r hr hk0 hk S)
      (olderExtendedConicOverlapSecond hπ data D j hj r hr hk0 hk S)
      (pullback.fst p P₁) (pullback.fst p P₂) :=
  PullbackOverlapBaseChange.isPullback H p

/-- The comparison with the actual parameter intersection after coefficient extension. -/
def olderExtendedConicOverlapIso : pullback p O ≅
    pullback (pullback.fst p P₁) (pullback.fst p P₂) :=
  (olderExtendedConicOverlap_isPullback hπ data D j hj r hr hk0 hk S).isoPullback

/-- The extended intersection comparison preserves the first ordered projection. -/
@[reassoc] theorem olderExtendedConicOverlapIso_first :
    (olderExtendedConicOverlapIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.fst (pullback.fst p P₁) (pullback.fst p P₂) =
        olderExtendedConicOverlapFirst hπ data D j hj r hr hk0 hk S :=
  (olderExtendedConicOverlap_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_fst

/-- The extended intersection comparison preserves the opposite ordered projection. -/
@[reassoc] theorem olderExtendedConicOverlapIso_second :
    (olderExtendedConicOverlapIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.snd (pullback.fst p P₁) (pullback.fst p P₂) =
        olderExtendedConicOverlapSecond hπ data D j hj r hr hk0 hk S :=
  (olderExtendedConicOverlap_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
