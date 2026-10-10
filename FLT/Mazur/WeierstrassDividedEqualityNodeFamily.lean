/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeCoproduct

/-!
# The original attachment family at equality depth

Only initial and retained ordered nodes occur. There is no extra terminal
node: the complete Laurent terminal component joins the last retained pair.
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
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The equality-depth attachment index, without a split terminal node. -/
abbrev EqualityNodeIndex (start s : ℕ) :=
  {_i : Fin 2 // 0 < start} ⊕ (Fin (s + 1) × Fin 2)

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (s + 1) hs)

/-- The actual initial and retained attachment sections in the fixed finite model. -/
def equalityNodeSection (i : EqualityNodeIndex start s) :
    Spec (.of K) ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  match i with
  | .inl a =>
    Fin.cases (initialGlobalFirstSection hπ data D (s + 1) hs a.property (by omega))
      (fun _ => initialGlobalSecondSection hπ data D (s + 1) hs a.property (by omega)) a.val
  | .inr a =>
    retainedNodeSectionAt hπ data D (s + 1) hs a.1.val (by omega) (by omega) a.2

/-- All original equality-depth attachments retain the coefficient structure. -/
@[reassoc] theorem equalityNodeSection_structure (i : EqualityNodeIndex start s) :
    equalityNodeSection hπ data D s hs hk i ≫ p = 𝟙 _ := by
  rcases i with ⟨a, ha⟩ | ⟨j, a⟩
  · fin_cases a
    · exact initialGlobalFirstSection_structure hπ data D (s + 1) hs ha (by omega)
    · exact initialGlobalSecondSection_structure hπ data D (s + 1) hs ha (by omega)
  · exact retainedNodeSectionAt_structure hπ data D (s + 1) hs j.val (by omega) (by omega) a

/-- Each retained ordered pair remains distinct in the equality-depth family. -/
theorem equalityNodeSection_retained_ne (j : Fin (s + 1)) :
    equalityNodeSection hπ data D s hs hk (.inr (j, 0)) ≠
      equalityNodeSection hπ data D s hs hk (.inr (j, 1)) :=
  retainedNodeSectionAt_ne hπ data D (s + 1) hs j.val (by omega) (by omega)

/-- The original attachment section viewed over the residue field. -/
def equalityNodeOverSection (i : EqualityNodeIndex start s) :
    PolygonPinching.point K ⟶ Over.mk p :=
  Over.homMk (equalityNodeSection hπ data D s hs hk i)
    (equalityNodeSection_structure hπ data D s hs hk i)

/-- The complete attachment leg for equality-depth component gluing. -/
def equalityNodeCoproductMap :
    (∐ fun _ : EqualityNodeIndex start s => PolygonPinching.point K) ⟶ Over.mk p :=
  Sigma.desc (equalityNodeOverSection hπ data D s hs hk)

/-- Every summand retains precisely its original section. -/
@[reassoc] theorem equalityNodeCoproductMap_ι (i : EqualityNodeIndex start s) :
    Sigma.ι (fun _ : EqualityNodeIndex start s => PolygonPinching.point K) i ≫
      equalityNodeCoproductMap hπ data D s hs hk =
        equalityNodeOverSection hπ data D s hs hk i := Sigma.ι_comp_desc _ _

end FLT.Mazur.WeierstrassDividedDepth
