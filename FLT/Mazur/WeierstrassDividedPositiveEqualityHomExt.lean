/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycleEndCharts
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialExt
public import FLT.Mazur.WeierstrassDividedPositiveEqualityIndexedExt
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCocone

/-!
# Arbitrary-target uniqueness for the actual positive-start equality cycle

The complete cyclic components determine morphisms from the entire original
model. The proof uses its finite open atlas, including both initial node opens;
the four-component case requires no separate redundancy assumption.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- The complete original cyclic components jointly detect arbitrary scheme morphisms. -/
theorem positiveEqualityCycleComponent_hom_ext : f = g := by
  apply (globalTensorOpenCover hπ data K (s + 1) hs).hom_ext
  intro i
  change Fin (s + 1 + 3) at i
  change globalTensorAtlasMap hπ data K (s + 1) hs i ≫ f =
    globalTensorAtlasMap hπ data K (s + 1) hs i ≫ g
  by_cases hzero : i.val = 0
  · have hi : i = 0 := Fin.ext hzero
    rw [hi]
    exact positiveEqualityCycleComponent_infinity_hom_ext hπ data D s hs hstart hk hp f g h
  by_cases hone : i.val = 1
  · have hi : i = Fin.succ 0 := Fin.ext hone
    rw [hi]
    exact positiveEqualityCycleComponent_terminal_hom_ext hπ data D s hs hstart hk hp f g h
  by_cases hlast : i.val = s + 3
  · have hi : i = ⟨s + 3, by omega⟩ := Fin.ext hlast
    rw [hi]
    exact positiveEqualityCycleComponent_initial_indexed_hom_ext
      hπ data D s hs hstart hk hp f g h
  by_cases hterminal : i.val = 2
  · have hi : i = ⟨2, by omega⟩ := Fin.ext hterminal
    rw [hi]
    exact positiveEqualityCycleComponent_terminal_indexed_hom_ext
      hπ data D s hs hstart hk hp f g h
  let j : Fin s := ⟨s + 2 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 2, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hi]
  exact positiveEqualityCycleComponent_earlier_indexed_hom_ext
    hπ data D s hs hstart hk hp f g h j

/-- The actual cyclic normalization leg is epimorphic over the residue field. -/
theorem positiveEqualityCycleNormalization_epi :
    Epi (positiveEqualityCycleNormalization hπ data D s hs hstart hk hp) where
  left_cancellation f g he := by
    apply Over.OverMorphism.ext
    apply positiveEqualityCycleComponent_hom_ext hπ data D s hs hstart hk hp f.left g.left
    intro i
    have H := congrArg (fun q => PolygonPinching.componentι K (2 * s + 4) i ≫ q) he
    simp only [positiveEqualityCycleNormalization_ι_assoc] at H
    exact congrArg Over.Hom.left H

end FLT.Mazur.WeierstrassDividedDepth
