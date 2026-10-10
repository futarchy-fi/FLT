/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleEndCharts
public import FLT.Mazur.WeierstrassDividedZeroEqualityIndexedExt
public import FLT.Mazur.WeierstrassDividedZeroEqualityCocone

/-!
# Actual cyclic components detect morphisms from the whole residue model

Equality is checked on the complete original finite open atlas, using the
scheme pushout on each retained node and the full exterior at infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h hpos in
/-- The actual complete cyclic components jointly detect scheme morphisms to any target. -/
theorem zeroEqualityCycleComponent_hom_ext_of_pos : f = g := by
  apply (globalTensorOpenCover hπ data K (s + 1) hs).hom_ext
  intro i
  change Fin (s + 1 + 3) at i
  change globalTensorAtlasMap hπ data K (s + 1) hs i ≫ f =
    globalTensorAtlasMap hπ data K (s + 1) hs i ≫ g
  by_cases hzero : i.val = 0
  · have hi : i = 0 := Fin.ext hzero
    rw [hi]
    exact zeroEqualityCycleComponent_infinity_hom_ext hπ data D s hs hstart hk hp f g h
  by_cases hone : i.val = 1
  · have hi : i = Fin.succ 0 := Fin.ext hone
    rw [hi]
    exact zeroEqualityCycleComponent_terminal_hom_ext hπ data D s hs hstart hk hp f g h
  by_cases hlast : i.val = s + 3
  · have hi : i = ⟨s + 3, by omega⟩ := Fin.ext hlast
    rw [hi]
    exact zeroEqualityCycleComponent_initial_hom_ext hπ data D s hs hstart hk hp f g h
  by_cases hold : i.val = s + 2
  · have hi : i = ⟨s + 2, by omega⟩ := Fin.ext hold
    rw [hi]
    exact zeroEqualityCycleComponent_zero_indexed_hom_ext hπ data D s hs
      hstart hk hp hpos f g h
  let j : Fin s := ⟨s + 1 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 1, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hi]
  exact zeroEqualityCycleComponent_positive_indexed_hom_ext hπ data D s hs
    hstart hk hp hpos f g h j

include hpos in
/-- The normalization leg of the actual cyclic cocone is epimorphic over the residue field. -/
theorem zeroEqualityCycleNormalization_epi_of_pos :
    Epi (zeroEqualityCycleNormalization hπ data D s hs hstart hk hp) where
  left_cancellation f g he := by
    apply Over.OverMorphism.ext
    apply zeroEqualityCycleComponent_hom_ext_of_pos hπ data D s hs
      hstart hk hp hpos f.left g.left
    intro i
    have H := congrArg (fun q => PolygonPinching.componentι K (2 * s + 2) i ≫ q) he
    simp only [zeroEqualityCycleNormalization_ι_assoc] at H
    exact congrArg Over.Hom.left H

end FLT.Mazur.WeierstrassDividedDepth
