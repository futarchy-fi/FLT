/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalAdjacentComponents
public import FLT.Mazur.WeierstrassDividedAdjacentComponentStructure
public import FLT.Mazur.WeierstrassDividedFinalNodeCoproduct

/-!
# All adjacent projective components as actual maps over the residue field

The original component family, with both exact node endpoints, gives the retained
part of the normalization coproduct. Exterior and terminal components are separate.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (s + 1) hs)

/-- Each complete adjacent component keeps the actual coefficient structure after transport. -/
@[reassoc] theorem finalAdjacentComponent_structure (j : Fin s) (i : Fin 2) :
    finalAdjacentComponent hπ data D s hs hk j i ≫ p = ProjectiveLine.toBase K := by
  rw [finalAdjacentComponent, Category.assoc,
    finiteGlobalTensorModel_structure_transport hπ data K _ _ (by omega),
    orderedAdjacentComponent_structure]

/-- The actual adjacent component over the residue field. -/
def finalAdjacentOverComponent (j : Fin s) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (finalAdjacentComponent hπ data D s hs hk j i)
    (finalAdjacentComponent_structure hπ data D s hs hk j i)

/-- Zero is the preceding original ordered node as a section over the field. -/
@[reassoc] theorem finalAdjacentOverComponent_zero (j : Fin s) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫ finalAdjacentOverComponent hπ data D s hs hk j i =
      finalNodeOverSection hπ data D s hs hk hp (.inl (.inr (⟨j.val, by omega⟩, i))) := by
  apply Over.OverMorphism.ext
  exact finalAdjacentComponent_zero hπ data D s hs hk hp j i

/-- Infinity is the next original ordered node as a section over the field. -/
@[reassoc] theorem finalAdjacentOverComponent_infinity (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫ finalAdjacentOverComponent hπ data D s hs hk j i =
      finalNodeOverSection hπ data D s hs hk hp (.inl (.inr (⟨j.val + 1, by omega⟩, i))) := by
  apply Over.OverMorphism.ext
  exact finalAdjacentComponent_infinity hπ data D s hs hk hp j i

include hp in
/-- Distinct retained levels or tangent orders cannot give the same full component map. -/
theorem finalAdjacentComponent_injective :
    Function.Injective (fun a : Fin s × Fin 2 =>
      finalAdjacentComponent hπ data D s hs hk a.1 a.2) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ he
  have H := congrArg (fun f => ProjectiveLine.zero K ≫ f) he
  rw [finalAdjacentComponent_zero hπ data D s hs hk hp,
    finalAdjacentComponent_zero hπ data D s hs hk hp] at H
  have hi := Prod.mk.inj (Sum.inr.inj (Sum.inl.inj
    (finalNodeSection_injective hπ data D s hs hk hp H)))
  exact Prod.ext (Fin.ext (congrArg (fun a : Fin (s + 1) => a.val) hi.1)) hi.2

/-- The entire adjacent part of the actual normalization coproduct over the field. -/
def finalAdjacentComponentCoproduct :
    (∐ fun _ : Fin s × Fin 2 => PolygonPinching.component K) ⟶ Over.mk p :=
  Sigma.desc (fun a => finalAdjacentOverComponent hπ data D s hs hk a.1 a.2)

/-- Every retained summand keeps its complete original component map. -/
@[reassoc] theorem finalAdjacentComponentCoproduct_ι (a : Fin s × Fin 2) :
    Sigma.ι (fun _ : Fin s × Fin 2 => PolygonPinching.component K) a ≫
        finalAdjacentComponentCoproduct hπ data D s hs hk =
      finalAdjacentOverComponent hπ data D s hs hk a.1 a.2 :=
  Sigma.ι_comp_desc _ _

end FLT.Mazur.WeierstrassDividedDepth
