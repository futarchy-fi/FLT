/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullRepresentation

/-!
# Geometry of the full original Picard test intersections

The full intersection embeds openly into test times translation base.
Consequently smooth or etale translation bases give smooth or etale actual
pullbacks of the glued map to the original Picard sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

instance baseMarkedFullToTest_smooth [Smooth V.hom] :
    Smooth (baseMarkedFullToTest f V a U s).left := by
  let _ : Smooth (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change Smooth ((baseMarkedFullInclusion f V a U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

instance baseMarkedFullToTest_etale [Etale V.hom] :
    Etale (baseMarkedFullToTest f V a U s).left := by
  let _ : Etale (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change Etale ((baseMarkedFullInclusion f V a U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

instance baseMarkedFullToTest_flat [Flat V.hom] :
    Flat (baseMarkedFullToTest f V a U s).left := by
  let _ : Flat (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change Flat ((baseMarkedFullInclusion f V a U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

instance baseMarkedFullToTest_locallyOfFinitePresentation [LocallyOfFinitePresentation V.hom] :
    LocallyOfFinitePresentation (baseMarkedFullToTest f V a U s).left := by
  let _ : LocallyOfFinitePresentation (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change LocallyOfFinitePresentation ((baseMarkedFullInclusion f V a U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

instance baseMarkedFullToTest_isOpenImmersion [IsOpenImmersion V.hom] :
    IsOpenImmersion (baseMarkedFullToTest f V a U s).left := by
  let _ : IsOpenImmersion (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change IsOpenImmersion ((baseMarkedFullInclusion f V a U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

end FLT.Mazur.HilbertChart
