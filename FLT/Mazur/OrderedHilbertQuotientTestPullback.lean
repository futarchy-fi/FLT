/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertOriginalTestCover
public import FLT.Mazur.OrderedHilbertIdentityQuotientOriginalSection

/-!
# Actual test pullbacks on the exact quotient-defined relative source

Transport the source endpoint through the proved coefficient comparison.
The intersection scheme, the test projection and the underlying source map
are unchanged. The result is the full pullback of the original Picard map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertOriginalTestIntersection
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (Z : Over (Spec (.of R))) (sZ : (relativeFppfSheaf f).obj.obj (op Z))

/-- The source endpoint on the exact scheme with its quotient-defined coefficient map. -/
def quotientFst : relation f hL Z sZ ⟶ quotientTest f hL :=
  fst f hL Z sZ ≫ (originalIso f hL).inv

/-- The underlying scheme arrow is unchanged. -/
theorem quotientFst_left : (quotientFst f hL Z sZ).left = (fst f hL Z sZ).left := by
  change (fst f hL Z sZ).left ≫ (𝟙 _) = _
  exact Category.comp_id _

/-- The original relative endpoint is recovered exactly. -/
@[reassoc]
theorem quotientFst_original :
    quotientFst f hL Z sZ ≫ (originalIso f hL).hom = fst f hL Z sZ := by
  simp only [quotientFst, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original test pulls back to the constructed geometric etale cover of that test. -/
theorem quotient_isPullback :
    IsPullback (uliftYoneda.{1}.map (quotientFst f hL Z sZ))
      (uliftYoneda.{1}.map (snd f hL Z sZ)) (quotientMap f hL) (testMap f Z sZ) := by
  refine (isPullback f hL Z sZ).of_iso' (Iso.refl _)
    (uliftYoneda.{1}.mapIso (originalIso f hL)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom,
      ← Functor.map_comp] using
      congrArg uliftYoneda.{1}.map (quotientFst_original f hL Z sZ).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id] using
      (quotientMap_eq f hL).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end FLT.Mazur.OrderedHilbertOriginalTestIntersection
