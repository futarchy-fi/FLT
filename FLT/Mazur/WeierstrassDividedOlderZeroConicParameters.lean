/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedConicOverlap
public import FLT.Mazur.WeierstrassModificationXConicZeroParameters

/-!
# Disjoint full conic charts at zero divided constant

At an older stage with vanishing divided constant, the two ordered full
parameter charts stay disjoint in the global model and after every
compatible coefficient extension. Neither component is discarded.
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

omit [IsDomain R] [IsBezout R] in
/-- A vanishing divided constant leaves no points in the full original overlap. -/
theorem olderGlobalZeroConicOverlap_isEmpty (hc : c = 0) :
    IsEmpty (Spec (.of (ConicParameterOverlap a c))) := by
  rw [hc]
  exact conicZeroOverlap_isEmpty a

/-- The original ordered conic parameter charts are disjoint in the retained global model. -/
theorem olderGlobalZeroConicParameters_disjoint (hc : c = 0) :
    Disjoint (Set.range P₁) (Set.range P₂) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let _ := olderGlobalZeroConicOverlap_isEmpty data j hj hc
  exact (olderGlobalConicOverlapIso hπ data D j hj r hr hk0 hk).symm.hom.homeomorph.isEmpty

/-- The full original overlap remains empty under coefficient extension. -/
theorem olderExtendedZeroConicOverlap_isEmpty (hc : c = 0) :
    IsEmpty (pullback p O : Scheme.{u}) := by
  let _ := olderGlobalZeroConicOverlap_isEmpty data j hj hc
  exact Function.isEmpty (pullback.snd p O)

/-- The actual extended ordered parameter charts remain disjoint when c vanishes. -/
theorem olderExtendedZeroConicParameters_disjoint (hc : c = 0) :
    Disjoint (Set.range (pullback.fst p P₁)) (Set.range (pullback.fst p P₂)) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let _ := olderExtendedZeroConicOverlap_isEmpty hπ data D j hj r hr hk0 hk S hc
  exact (olderExtendedConicOverlapIso hπ data D j hj r hr hk0 hk S).symm.hom.homeomorph.isEmpty

end FLT.Mazur.WeierstrassDividedDepth
