/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldTranslation
public import FLT.Mazur.PolygonCyclicBoundaryNodeFrame
public import FLT.Mazur.PolygonParameterNormalizationLine

/-!
# Node frames in intrinsic boundary field coordinates

The coefficient-point comparison retains every original translated node. Its
marking-line frame preserves the exact unit section under the intrinsic field
translation and under the common finite relabeling.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "F" => Over.pullback (g)
variable (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
  CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)

/-- The original node followed by the intrinsic extension-field translation. -/
def extendedNode : (F).obj (point K) ⟶ (F).obj C :=
  (F).map (nodeι K m k ≫ q) ≫ extendedTranslation K L m hm p q h n f j

/-- The intrinsic translated node is the original translated node map. -/
theorem extendedNode_eq :
    (extendedNode K L m hm p q h n f j k).left =
      labelNode K m hm p q h n (g) f j k := by
  rw [extendedNode, ← extendedTranslation_iso_hom, Over.comp_left]
  rfl

/-- Field-point coordinates retain the actual translated node on the original cocone. -/
@[reassoc] theorem extendedNode_coordinates :
    (ProjectiveLineFieldExtension.pointIso K L).hom ≫
        extendedNode K L m hm p q h n f j k =
      nodeι L m k ≫ PolygonActionFieldExtension.nodeMap K L m q ≫
        extendedTranslation K L m hm p q h n f j := by
  have hi : nodeι L m k ≫ (PolygonFieldExtension.nodesIso K L m).hom =
      (ProjectiveLineFieldExtension.pointIso K L).hom ≫ (F).map (nodeι K m k) :=
    PolygonFieldExtension.inclusion K L (fun _ : Fin m ↦ point K)
      (fun _ ↦ point L) (fun _ ↦ ProjectiveLineFieldExtension.pointIso K L) k
  simp only [extendedNode, PolygonActionFieldExtension.nodeMap,
    Functor.map_comp, ← Category.assoc]
  rw [hi]

/-- The canonical frame transported to the intrinsic field-coordinate node. -/
def extendedNodeFrame :
    (Scheme.Modules.pullback (extendedNode K L m hm p q h n f j k).left).obj
      (divisorLineBundle (labelIdeal K m hm p q h n (g) f a i j)
        (labelIdeal_cartier K m hm p q h n (g) f a i j).1) ≅
      divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackCongr (extendedNode_eq K L m hm p q h n f j k)).app _ ≪≫
    labelNodeFrame K m hm p q h n (g) f a i j k

/-- The transported node frame retains the complete canonical section. -/
theorem extendedNodeFrame_section :
    DivisorLineSectionCompatible (extendedNode K L m hm p q h n f j k).left
      (labelIdeal_cartier K m hm p q h n (g) f a i j).1 effectiveCartier_top
      (extendedNodeFrame K L m hm p q h n f a i j k) :=
  (movedNodeLineIso_section K m hm p q h (g) (c) a i k).congr _

/-- The intrinsic node frame has unit section exactly, with no unspecified scalar. -/
@[reassoc] theorem extendedNodeFrame_unit :
    (Scheme.Modules.pullback (extendedNode K L m hm p q h n f j k).left).map
        (divisorSectionMap (labelIdeal_cartier K m hm p q h n (g) f a i j).1) ≫
      (extendedNodeFrame K L m hm p q h n f a i j k).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso (extendedNode K L m hm p q h n f j k).left).hom := by
  rw [← Category.assoc, (extendedNodeFrame_section K L m hm p q h n f a i j k).section,
    Category.assoc, divisorSection_top_map, Iso.inv_hom_id, Category.comp_id]

/-- Common finite relabeling retains the intrinsic translated node map. -/
theorem extendedNode_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    extendedNode K L m hm p q h n (f ≫ (action (G K m) n r).hom) j k =
      extendedNode K L m hm p q h n f (r.2.2.symm j) k := by
  rw [extendedNode, extendedNode, extendedTranslation_action]

end FLT.Mazur.PolygonCyclicBoundary
