/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalChainRestrictions
public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalExteriorRestriction
public import FLT.Mazur.WeierstrassDividedZeroEqualityUniversalHomExt
public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalTerminalRestriction
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalTerminalRestriction
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalChainRestrictions
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalExteriorRestriction

/-!
# Global descent restricts to every complete cyclic component

The actual component maps satisfy existence and uniqueness of descent for
every compatible family of morphisms to an arbitrary scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- Every complete original cyclic component recovers its prescribed family map. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_component (i : Fin (2 * s + 2)) :
    (Z i).left ≫ d = F i := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    exact zeroEqualityPositiveCycleGlobalDesc_exterior_component
      hπ data D s hs hstart hk hp hpos F w
  by_cases ht : i.val = s + 1
  · have hi : i = ⟨s + 1, by omega⟩ := Fin.ext ht
    rw [hi]
    exact zeroEqualityPositiveCycleGlobalDesc_terminal_component
      hπ data D s hs hstart hk hp hpos F w
  by_cases hfirst : i.val ≤ s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have hi : (⟨j.val + 1, by omega⟩ : Fin (2 * s + 2)) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hi] using
      zeroEqualityPositiveCycleGlobalDesc_first_component hπ data D s hs hstart hk hp hpos F w j
  · let j : Fin s := ⟨2 * s + 1 - i.val, by omega⟩
    have hi : (⟨2 * s + 1 - j.val, by omega⟩ : Fin (2 * s + 2)) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hi] using
      zeroEqualityPositiveCycleGlobalDesc_second_component hπ data D s hs hstart hk hp hpos F w j

/-- The actual full component restrictions uniquely characterize the global descent. -/
theorem zeroEqualityPositiveCycleGlobalDesc_component_unique
    (f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hf : ∀ i, (Z i).left ≫ f = F i) : f = d := by
  apply zeroEqualityCycleComponent_hom_ext hπ data D s hs hstart hk hp
  intro i
  exact (hf i).trans (zeroEqualityPositiveCycleGlobalDesc_component
      hπ data D s hs hstart hk hp hpos F w i).symm

include w in
/-- Every compatible projective family descends uniquely to the actual full residue model. -/
theorem zeroEqualityPositiveCycle_existsUnique_desc :
    ∃! f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y,
      ∀ i, (Z i).left ≫ f = F i :=
  ⟨d, zeroEqualityPositiveCycleGlobalDesc_component hπ data D s hs hstart hk hp hpos F w,
    fun f hf => zeroEqualityPositiveCycleGlobalDesc_component_unique
      hπ data D s hs hstart hk hp hpos F w f hf⟩

end FLT.Mazur.WeierstrassDividedDepth
