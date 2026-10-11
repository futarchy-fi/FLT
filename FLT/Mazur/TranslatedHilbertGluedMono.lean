/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedMap
public import FLT.Mazur.OverOpenCoverExt

/-!
# Injectivity of the glued translated Picard map

The original chart classes distinguish local maps. Pulling back the actual
open chart cover twice shows the global map distinguishes every relative test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)

/-- The glued original Picard map distinguishes all maps on every relative test. -/
theorem translatedHilbertGluedPoint_injective (U : Over (Spec (.of R))) :
    Function.Injective (translatedHilbertGluedPoint f hL a U) := by
  intro p q hpq
  apply over_hom_ext_of_openCover_factorizations
    (fun i ↦ acyclicHilbertTest f (a i).1) (translatedHilbertGluedArrow f hL a)
    (translatedHilbertGluedCover f hL a).mem₀ p q
  intro i V d u hdu
  symm
  apply over_hom_ext_of_openCover_factorizations
    (fun i ↦ acyclicHilbertTest f (a i).1) (translatedHilbertGluedArrow f hL a)
    (translatedHilbertGluedCover f hL a).mem₀ (d ≫ q) (d ≫ p)
  intro j W e v hev
  have hleft : e ≫ (d ≫ p) = (e ≫ u) ≫ translatedHilbertGluedArrow f hL a i := by
    rw [hdu, Category.assoc]
  have hc : translatedHilbertGluedPoint f hL a W (e ≫ (d ≫ p)) =
      translatedHilbertGluedPoint f hL a W (e ≫ (d ≫ q)) := by
    simpa only [← translatedHilbertGluedPoint_natural, Category.assoc] using
      congrArg ((relativeFppfSheaf f).obj.map (e ≫ d).op) hpq
  rw [hleft, hev, translatedHilbertGluedPoint_chart, translatedHilbertGluedPoint_chart] at hc
  exact hev.trans ((translatedHilbertGlued_chart_class_eq f hL a i j (e ≫ u) v hc).symm.trans
    hleft.symm)

/-- The natural transformation to the original Picard presheaf is a monomorphism. -/
instance translatedHilbertGluedPicardMap_mono : Mono (translatedHilbertGluedPicardMap f hL a) := by
  suffices ∀ U, Mono ((translatedHilbertGluedPicardMap f hL a).app U) from
    NatTrans.mono_of_mono_app _
  intro U
  rw [CategoryTheory.mono_iff_injective]
  intro p q hpq
  apply ULift.ext
  exact translatedHilbertGluedPoint_injective f hL a U.unop hpq

end FLT.Mazur.HilbertChart
