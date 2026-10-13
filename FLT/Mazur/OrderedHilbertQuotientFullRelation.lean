/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityQuotientOriginalSection
public import FLT.Mazur.OrderedHilbertIdentityRelationOperations

/-!
# The full original relation over the quotient-defined relative source

Transport only the endpoints across the proved identity-source base comparison.
The relation scheme and all its independent coordinates remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertQuotientFullRelation
open HilbertChart CartierAbel SchemePicard FCurve
open OrderedHilbertIdentityQuotientOriginalSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "A" => OrderedHilbertIdentityOriginalRelation.relation f hL
local notation "p" => OrderedHilbertIdentityOriginalRelation.fst f hL
local notation "q" => OrderedHilbertIdentityOriginalRelation.snd f hL

/-- The original first endpoint on the exact quotient-defined relative source. -/
def fst : A ⟶ quotientTest f hL := p ≫ (originalIso f hL).inv

/-- The original second endpoint, retaining the entire relation scheme. -/
def snd : A ⟶ quotientTest f hL := q ≫ (originalIso f hL).inv

/-- The scheme map of the first endpoint has not changed. -/
theorem fst_left : (fst f hL).left = (p).left := by
  change (p).left ≫ (𝟙 _) = (p).left
  exact Category.comp_id _

/-- The scheme map of the second endpoint has not changed. -/
theorem snd_left : (snd f hL).left = (q).left := by
  change (q).left ≫ (𝟙 _) = (q).left
  exact Category.comp_id _

instance fst_etale : Etale (fst f hL).left := by
  rw [fst_left]
  infer_instance

instance snd_etale : Etale (snd f hL).left := by
  rw [snd_left]
  infer_instance

/-- Both original endpoints recover their original relative arrows. -/
@[reassoc]
theorem fst_original : fst f hL ≫ (originalIso f hL).hom = p := by
  simp only [fst, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc]
theorem snd_original : snd f hL ≫ (originalIso f hL).hom = q := by
  simp only [snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- All original equal-class pairs form the kernel pair on the exact relative source. -/
theorem isPullback :
    IsPullback (uliftYoneda.{1}.map (fst f hL)) (uliftYoneda.{1}.map (snd f hL))
      (quotientMap f hL) (quotientMap f hL) := by
  refine (OrderedHilbertIdentityOriginalRelation.isPullback f hL).of_iso'
    (Iso.refl _) (uliftYoneda.{1}.mapIso (originalIso f hL))
    (uliftYoneda.{1}.mapIso (originalIso f hL)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom,
      ← Functor.map_comp] using congrArg uliftYoneda.{1}.map (fst_original f hL).symm
  · simpa only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom,
      ← Functor.map_comp] using congrArg uliftYoneda.{1}.map (snd_original f hL).symm
  · simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id] using
      (quotientMap_eq f hL).symm
  · simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id] using
      (quotientMap_eq f hL).symm

end FLT.Mazur.OrderedHilbertQuotientFullRelation
