/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenSpectrumImage
public import FLT.Mazur.GeneralizedCurveMarkingAffineDiagram

/-!
# Exact original-base images of the direct cubic restrictions

Every directly framed cubic carries its actual original base morphism.
Restriction images are precisely inverse images of the smaller base opens,
which permits common refinements without affine intersections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

local instance affineRangeNoetherian (i : SmoothMarkingAffineChart E s) :
    IsNoetherianRing Γ(i.base.1.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The actual structure map to the original affine chart base. -/
def smoothMarkingAffineStructure (i : SmoothMarkingAffineChart E s) :
    (smoothMarkingAffineDiagram E s).obj i ⟶ i.base.1.toScheme :=
  integralCurveStructure (smoothMarkingAffineEquation E s i) ≫ i.base.1.toScheme.isoSpec.inv

/-- The actual structure map to the whole original base. -/
def smoothMarkingAffineBase (i : SmoothMarkingAffineChart E s) :
    (smoothMarkingAffineDiagram E s).obj i ⟶ S :=
  smoothMarkingAffineStructure E s i ≫ i.base.1.ι

/-- Direct restriction maps retain their original affine bases. -/
@[reassoc] theorem smoothMarkingAffineStructure_naturality
    {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    (smoothMarkingAffineDiagram E s).map f ≫ smoothMarkingAffineStructure E s j =
      smoothMarkingAffineStructure E s i ≫ S.homOfLE f.le := by
  change smoothMarkingDirectRestriction E s j.base.1 i.base.1 f.le j.frame i.frame ≫
    (integralCurveStructure _ ≫ _) = _
  rw [← Category.assoc, smoothMarkingDirectRestriction_over, Category.assoc,
    affineOpenSpectrumMap_eq j.base.1 i.base.1 f.le]
  simp only [smoothMarkingAffineStructure, smoothMarkingAffineEquation,
    Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The whole-base maps form a cocone on the constructed diagram. -/
@[reassoc] theorem smoothMarkingAffineBase_naturality
    {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    (smoothMarkingAffineDiagram E s).map f ≫ smoothMarkingAffineBase E s j =
      smoothMarkingAffineBase E s i := by
  rw [smoothMarkingAffineBase, ← Category.assoc,
    smoothMarkingAffineStructure_naturality, Category.assoc, Scheme.homOfLE_ι]
  rfl

/-- A cubic chart lies over its actual original base open. -/
theorem smoothMarkingAffineBase_mem (i : SmoothMarkingAffineChart E s)
    (x : (smoothMarkingAffineDiagram E s).obj i) : smoothMarkingAffineBase E s i x ∈ i.base.1 :=
  (smoothMarkingAffineStructure E s i x).property

/-- The entire cubic restriction image is exactly the inverse image of the smaller base open. -/
theorem smoothMarkingAffineDiagram_range {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    Set.range ((smoothMarkingAffineDiagram E s).map f) =
      smoothMarkingAffineBase E s j ⁻¹' (i.base.1 : Set S) := by
  change Set.range (smoothMarkingDirectRestriction E s j.base.1 i.base.1 f.le
    j.frame i.frame) = _
  unfold smoothMarkingDirectRestriction
  rw [scheme_range_comp_of_isIso]
  change Set.range (smoothMarkingCubicProjection _ _ _ _ _) = _
  rw [smoothMarkingCubicProjection_range]
  ext x
  exact mem_affineOpenSpectrumMap_range j.base.1 i.base.1 f.le _

end FLT.Mazur.GeneralizedEllipticCurve
