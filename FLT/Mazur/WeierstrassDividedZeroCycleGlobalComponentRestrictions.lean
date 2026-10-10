/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalChainRestrictions
public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalExteriorRestriction
public import FLT.Mazur.WeierstrassDividedZeroCycleHomExt
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalChainRestrictions
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalExteriorRestriction

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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- Every complete original cyclic component recovers its prescribed family map. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_component (i : Fin (2 * s + 3)) :
    (Z i).left ≫ d = F i := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    exact zeroSplitCycleGlobalDesc_exterior_component hπ data D s hs hstart hp F w
  by_cases hfirst : i.val ≤ s + 1
  · let j : Fin (s + 1) := ⟨i.val - 1, by omega⟩
    have hi : (⟨j.val + 1, by omega⟩ : Fin (2 * s + 3)) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hi] using
      zeroSplitCycleGlobalDesc_first_component hπ data D s hs hstart hp F w j
  · let j : Fin (s + 1) := ⟨2 * s + 2 - i.val, by omega⟩
    have hi : (⟨2 * s + 2 - j.val, by omega⟩ : Fin (2 * s + 3)) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [hi] using
      zeroSplitCycleGlobalDesc_second_component hπ data D s hs hstart hp F w j

/-- The actual full component restrictions uniquely characterize the global descent. -/
theorem zeroSplitCycleGlobalDesc_component_unique
    (f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hf : ∀ i, (Z i).left ≫ f = F i) : f = d := by
  apply zeroSplitCycleComponent_hom_ext hπ data D s hs hstart (by omega) hp
  intro i
  exact (hf i).trans (zeroSplitCycleGlobalDesc_component hπ data D s hs hstart hp F w i).symm

include w in
/-- Every compatible projective family descends uniquely to the actual full residue model. -/
theorem zeroSplitCycle_existsUnique_desc :
    ∃! f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y,
      ∀ i, (Z i).left ≫ f = F i :=
  ⟨d, zeroSplitCycleGlobalDesc_component hπ data D s hs hstart hp F w,
    fun f hf => zeroSplitCycleGlobalDesc_component_unique hπ data D s hs hstart hp F w f hf⟩

end FLT.Mazur.WeierstrassDividedDepth
