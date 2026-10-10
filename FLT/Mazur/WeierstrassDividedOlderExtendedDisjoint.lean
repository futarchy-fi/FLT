/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSectionSquares
public import FLT.Mazur.WeierstrassDividedOlderExtendedComponentOrigins
public import FLT.Mazur.WeierstrassDividedOlderGlobalIntersections
public import FLT.Mazur.PullbackOverlapBaseChange
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections

/-!
# Empty ordered line intersection after coefficient extension

The actual extended horizontal lines remain disjoint. Their full intersection
square is the empty scheme square, including arbitrary coefficient algebras.
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

/-- The complete coefficient extension of the original empty overlap is empty. -/
theorem olderExtendedMiddleLines_isEmpty :
    IsEmpty (pullback (pullback.fst p L₁) (pullback.fst p L₂) : Scheme.{u}) := by
  have H := olderGlobalMiddleLines_isPullback hπ data D j hj r hr hk0 hk
  have Q := PullbackOverlapBaseChange.isPullback H p
  let _ : IsEmpty (pullback p (Scheme.emptyTo _ ≫ L₁) : Scheme.{u}) :=
    Function.isEmpty (pullback.snd p (Scheme.emptyTo _ ≫ L₁))
  exact Q.isoPullback.symm.hom.homeomorph.isEmpty

/-- No point lies on both actual extended ordered lines. -/
theorem olderExtendedMiddleLines_disjoint :
    Disjoint (Set.range (pullback.fst p L₁)) (Set.range (pullback.fst p L₂)) :=
  Scheme.isEmpty_pullback_iff.mp
    (olderExtendedMiddleLines_isEmpty hπ data D j hj r hr hk0 hk S)

/-- The original ordering determines the empty full intersection square after extension. -/
theorem olderExtendedMiddleLines_isPullback :
    IsPullback (Scheme.emptyTo (pullback p L₁)) (Scheme.emptyTo (pullback p L₂))
      (pullback.fst p L₁) (pullback.fst p L₂) := by
  let _ := olderExtendedMiddleLines_isEmpty hπ data D j hj r hr hk0 hk S
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (pullback.fst p L₁) (pullback.fst p L₂))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
