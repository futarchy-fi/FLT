/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonActionFieldExtension
public import FLT.Mazur.PolygonActionGraph

/-!
# Geometric rotations of the actual pulled-back polygon action

The actual group pullback has extension-field coordinates. Specializing its
actual pulled-back action at arbitrary extension-field units and components
rotates all geometric irreducible components and nodes with cyclic incidence.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonGeometricTranslations
open PolygonPinching PolygonActionGraph PolygonActionFieldExtension ProjectiveLineProductCharts
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "F" => Over.pullback (parameterToBase K L)
local notation "pL" => normalization K L n p
local notation "qL" => nodeMap K L n q
local notation "hL" => cocone K L n hn p q h

/-- A translation of the actual pulled-back action by any extension-field unit and component. -/
def translation (a : Lˣ) (b : ZMod n) : (F).obj C ⟶ (F).obj C :=
  (λ_ ((F).obj C)).inv ≫
    (PolygonActionTranslation.groupPoint L n a b ≫ (groupIso K L n).hom) ▷ (F).obj C ≫
      PolygonActionBaseChange.baseChangedAct K n hn p q h (parameterToBase K L)

/-- Arbitrary extension-field translations coincide with the intrinsic polygon translations. -/
theorem translation_eq (a : Lˣ) (b : ZMod n) :
    translation K L n hn p q h a b =
      PolygonActionTranslation.translation L n hn (pL) (qL) (hL) a b := by
  simp only [translation, comp_whiskerRight, Category.assoc, PolygonActionFieldExtension.action]
  rfl

/-- The actual pulled-back action rotates geometric irreducible components. -/
theorem component_rotation (a : Lˣ) (b : ZMod n) (i : Fin n) :
    (translation K L n hn p q h a b).left '' (vertices L n hn (pL) (qL) (hL) i).val =
      (vertices L n hn (pL) (qL) (hL) (rotateIndex b i)).val := by
  rw [translation_eq]
  exact vertex_translation L n hn (pL) (qL) (hL) a b i

/-- The actual pulled-back action rotates geometric nodes with their cyclic incidence. -/
theorem node_rotation (a : Lˣ) (b : ZMod n) (j : Fin n) :
    let := polygon_lfp L n hn (pL) (qL) (hL)
    (translation K L n hn p q h a b).left (edges L n hn (pL) (qL) (hL) j).val =
      (edges L n hn (pL) (qL) (hL) (rotateIndex b j)).val := by
  let := polygon_lfp L n hn (pL) (qL) (hL)
  dsimp only
  rw [translation_eq]
  exact edge_translation L n hn (pL) (qL) (hL) a b j

/-- Both branches of the actual geometric graph rotate together. -/
theorem incidence_rotation (b : ZMod n) (i j : Fin n) :
    let := polygon_lfp L n hn (pL) (qL) (hL)
    (edges L n hn (pL) (qL) (hL) (rotateIndex b j)).val ∈
      (vertices L n hn (pL) (qL) (hL) (rotateIndex b i)).val ↔
    (edges L n hn (pL) (qL) (hL) j).val ∈ (vertices L n hn (pL) (qL) (hL) i).val := by
  let := polygon_lfp L n hn (pL) (qL) (hL)
  exact PolygonActionGraph.rotation_incidence L n hn (pL) (qL) (hL) b i j
end FLT.Mazur.PolygonGeometricTranslations
