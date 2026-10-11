/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalExteriorRestriction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalLineRestrictions
public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalConicRestrictions
public import FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalTerminalRestriction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityHomExt
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalExteriorRestriction
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalLineRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalConicRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalTerminalRestriction
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalInitialRestrictions
import all FLT.Mazur.WeierstrassDividedPositiveEqualityGlobalDesc

/-!
# Every full cyclic component recovers its prescribed map

The original affine charts cover each chain component. The exterior and
terminal restrictions complete the cycle, also when it has four components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => positiveEqualityCycleGlobalDesc hπ data D s hs hstart hk hp F w
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
/-- Every first-chain component recovers its entire prescribed projective map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_first_component (j : Fin (s + 1)) :
    (Z ⟨j.val + 1, by omega⟩).left ≫ d = F ⟨j.val + 1, by omega⟩ := by
  apply pushout.hom_ext
  · exact positiveEqualityCycleGlobalDesc_retained_first_line
      hπ data D s hs hstart hk hp F w j.val (by omega)
  · change ProjectiveLine.right K ≫ (Z ⟨j.val + 1, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 1, by omega⟩
    by_cases hz : j.val = 0
    · have hi : (⟨j.val + 1, by omega⟩ : Fin (2 * s + 4)) = 1 := by
        apply Fin.ext
        change j.val + 1 = 1 % (2 * s + 4)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hi]
      exact positiveEqualityCycleGlobalDesc_initial_first_chart hπ data D s hs hstart hk hp F w
    · have hj : j.val - 1 + 2 = j.val + 1 := by omega
      simpa only [hj] using positiveEqualityCycleGlobalDesc_interior_first_conic
        hπ data D s hs hstart hk hp F w ⟨j.val - 1, by omega⟩

/-- Every opposite-chain component recovers its entire prescribed projective map. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_second_component (j : Fin (s + 1)) :
    (Z ⟨2 * s + 3 - j.val, by omega⟩).left ≫ d = F ⟨2 * s + 3 - j.val, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ (Z ⟨2 * s + 3 - j.val, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 3 - j.val, by omega⟩
    by_cases hz : j.val = 0
    · simpa only [hz, Nat.sub_zero] using
        positiveEqualityCycleGlobalDesc_initial_second_chart hπ data D s hs hstart hk hp F w
    · have hj : 2 * s + 2 - (j.val - 1) = 2 * s + 3 - j.val := by omega
      simpa only [hj] using positiveEqualityCycleGlobalDesc_interior_second_conic
        hπ data D s hs hstart hk hp F w ⟨j.val - 1, by omega⟩
  · exact positiveEqualityCycleGlobalDesc_retained_second_line
      hπ data D s hs hstart hk hp F w j.val (by omega)

/-- The actual global descent recovers every complete cyclic component. -/
@[reassoc] theorem positiveEqualityCycleGlobalDesc_component (i : Fin (2 * s + 4)) :
    (Z i).left ≫ d = F i := by
  by_cases hz : i.val = 0
  · have hi : i = 0 := Fin.ext hz
    subst i
    exact positiveEqualityCycleGlobalDesc_exterior_component hπ data D s hs hstart hk hp F w
  by_cases hf : i.val ≤ s + 1
  · have hi : i = ⟨(i.val - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi]
    exact positiveEqualityCycleGlobalDesc_first_component
      hπ data D s hs hstart hk hp F w ⟨i.val - 1, by omega⟩
  by_cases ht : i.val = s + 2
  · have hi : i = ⟨s + 2, by omega⟩ := Fin.ext ht
    rw [hi]
    exact positiveEqualityCycleGlobalDesc_terminal_component hπ data D s hs hstart hk hp F w
  have hi : i = ⟨2 * s + 3 - (2 * s + 3 - i.val), by omega⟩ := Fin.ext (by dsimp; omega)
  rw [hi]
  exact positiveEqualityCycleGlobalDesc_second_component
    hπ data D s hs hstart hk hp F w ⟨2 * s + 3 - i.val, by omega⟩

include w in
/-- Compatible projective families have unique descent to the entire original model. -/
theorem positiveEqualityCycle_existsUnique_desc :
    ∃! q : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y,
      ∀ i, (Z i).left ≫ q = F i := by
  refine ⟨d, positiveEqualityCycleGlobalDesc_component hπ data D s hs hstart hk hp F w, ?_⟩
  intro q hq
  apply positiveEqualityCycleComponent_hom_ext hπ data D s hs hstart hk hp
  intro i
  exact (hq i).trans
    (positiveEqualityCycleGlobalDesc_component hπ data D s hs hstart hk hp F w i).symm

end FLT.Mazur.WeierstrassDividedDepth
