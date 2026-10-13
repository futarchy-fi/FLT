/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTranslation
public import FLT.Mazur.PolygonParameterProductNode

/-!
# Original node frames of the complete smoothing product

The complete product is the unit ideal at each original parameter node. Its
canonical section has coordinate one in the original empty-divisor frame;
varying translation gives the same frame through the actual recovery triangle.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonPinching
  PolygonMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- Each original parameter node maps into the complete smoothing. -/
def completeBoundaryNodeMap (i : Fin n) :
    ((Over.pullback g).obj (point K)).left ⟶ exactVeroneseProj K n h :=
  ((Over.pullback g).map (nodeι K n i ≫ q)).left ≫
    completeBoundaryParameterMap K n h g

/-- The complete product is the unit ideal on every original parameter node. -/
theorem completeMarkingDivisor_node (i : Fin n) :
    (completeMarkingDivisor K n h).comap (completeBoundaryNodeMap K n h g i) = ⊤ := by
  rw [completeBoundaryNodeMap, Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_boundaryParameter, productMarkingIdeal_node K n hn p q hp]

/-- The complete positive line retains the original empty-divisor node frame. -/
def completeBoundaryNodeLineIso (i : Fin n) :
    (Scheme.Modules.pullback (completeBoundaryNodeMap K n h g i)).obj
      (completeMarkingLine K n h) ≅ divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeBoundaryParameterLineIso K n h g) ≪≫
      productNodeLineIso K n hn p q hp g (fun _ ↦ 1) i

/-- The complete node comparison preserves the canonical section without rescaling. -/
theorem completeBoundaryNodeLineIso_section (i : Fin n) :
    DivisorLineSectionCompatible (completeBoundaryNodeMap K n h g i)
      (completeMarkingDivisor_relativeCartier K n h).1 effectiveCartier_top
      (completeBoundaryNodeLineIso K n h g i) :=
  (completeBoundaryParameterLineIso_section K n h g).comp
    (productNodeLineIso_section K n hn p q hp g (fun _ ↦ 1) i)

/-- The complete product section has coordinate one in the original node frame. -/
@[reassoc] theorem completeBoundaryNodeLineIso_unit (i : Fin n) :
    (Scheme.Modules.pullback (completeBoundaryNodeMap K n h g i)).map
      (divisorSectionMap (completeMarkingDivisor_relativeCartier K n h).1) ≫
        (completeBoundaryNodeLineIso K n h g i).hom ≫
          (divisorLineBundleTopIso effectiveCartier_top).hom =
            (modulePullbackUnitIso _).hom :=
  (completeBoundaryNodeLineIso_section K n h g i).unit _

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (i : Fin n)
local notation "ν" => Over.Hom.left
  (CategoryTheory.Functor.map (Over.pullback g) (nodeι K n i ≫ q)) ≫
    Over.Hom.left (Iso.hom (translationIso K n hn p q hp g c))

/-- Translated node recovers the very same original complete-family map. -/
theorem completeBoundaryNodeMap_translation :
    (ν) ≫ completeMovedBoundaryMap K n h g c =
      completeBoundaryNodeMap K n h g i := by
  rw [Category.assoc, translation_completeMovedBoundaryMap]
  rfl

/-- The complete and translated node comparisons form the actual line triangle. -/
theorem completeBoundaryNodeLineIso_triangle :
    LinePullbackTriangle (ν) (completeMovedBoundaryMap K n h g c)
      (completeBoundaryNodeMap K n h g i)
      (completeBoundaryNodeMap_translation K n h g c i)
      (completeMovedBoundaryLineIso K n h g c)
      (movedProductNodeLineIso K n hn p q hp g c (fun _ ↦ 1) i)
      (completeBoundaryNodeLineIso K n h g i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMovedBoundaryLineIso_section K n h g c)
    (movedProductNodeLineIso_section K n hn p q hp g c (fun _ ↦ 1) i)
    (completeBoundaryNodeLineIso_section K n h g i)

end FLT.Mazur.PolygonInfinitesimalStages
