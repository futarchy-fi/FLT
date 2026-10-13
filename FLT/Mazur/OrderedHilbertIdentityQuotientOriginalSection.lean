/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityOriginalBaseSquare
public import FLT.Mazur.OrderedHilbertIdentitySheafCoverage

/-!
# The original Picard map on the exact quotient-defined source

The proved equality of coefficient morphisms identifies the original section
with a section on W240's exact source and base. Its map covers the same sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityQuotientOriginalSection
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertIdentityOriginalSection
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hL
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "m" => OrderedHilbertIdentityOriginalRelation.sourceMap f hL

/-- W240's exact scheme source with its quotient-defined coefficient morphism. -/
def quotientTest : Over (Spec (.of R)) :=
  Over.mk (OrderedHilbertIdentitySchemeSource.base f hL)

/-- The original relative test identification uses the identity on the underlying scheme. -/
def originalIso : quotientTest f hL ≅ U :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ (sourceTest f hL).hom = OrderedHilbertIdentitySchemeSource.base f hL
    rw [Category.id_comp]
    exact OrderedHilbertIdentityOriginalBaseSquare.source_base f hL)

/-- No scheme source is replaced in the coefficient comparison. -/
theorem originalIso_hom_left : (originalIso f hL).hom.left = 𝟙 _ := rfl

/-- The ORIGINAL Picard section on the source with its quotient-defined base. -/
def quotientSection : (relativeFppfSheaf f).obj.obj (op (quotientTest f hL)) :=
  (relativeFppfSheaf f).obj.map (originalIso f hL).hom.op sU

/-- The associated map still lands in the ORIGINAL fppf Picard sheaf. -/
def quotientMap : uliftYoneda.{1}.obj (quotientTest f hL) ⟶
    (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm (quotientSection f hL)

/-- Equality with the original Picard map holds on every original relative test. -/
theorem quotientMap_eq : quotientMap f hL = uliftYoneda.{1}.map (originalIso f hL).hom ≫ m := by
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro q
  change (relativeFppfSheaf f).obj.map q.down.op
      ((relativeFppfSheaf f).obj.map (originalIso f hL).hom.op sU) =
    (relativeFppfSheaf f).obj.map (q.down ≫ (originalIso f hL).hom).op sU
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The exact quotient-defined relative source covers the ORIGINAL Picard sheaf. -/
instance quotientMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (quotientMap f hL) := by
  rw [quotientMap_eq]
  infer_instance

end FLT.Mazur.OrderedHilbertIdentityQuotientOriginalSection
