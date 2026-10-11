/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertTranslationCover

/-!
# Original Picard descent along actual translation-base covers

The constructed changed schemes give an fppf covering family. The original
Picard sheaf therefore has unique descent along these actual scheme maps.
This is section descent; scheme effectivity of the full quotient is separate.
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
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  {κ : Type} (W : κ → Over (Spec (.of R))) (b : ∀ j, W j ⟶ V)
  (hb : ∀ x : V.left, ∃ j, ∃ y : (W j).left, (b j).left y = x)
  [∀ j, Flat (b j).left] [∀ j, LocallyOfFinitePresentation (b j).left]
local notation "G" j => baseMarkedGluedTest f hL (W j)
  (fun i ↦ baseMarkedIndexChange f (b j) (a i))

include hb

/-- The induced actual scheme family is a covering sieve for the original fppf sheaf. -/
theorem baseMarkedTranslation_isSheafFor :
    Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows (fun j ↦ G j) (fun j ↦ baseMarkedGluedChange f hL (b j) a)) := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  apply hs.isSheafFor
  rw [GrothendieckTopology.mem_over_iff, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (baseMarkedGluedChangeCover f hL V a W b (@Flat ⊓ @LocallyOfFinitePresentation)
      hb (fun j ↦ ⟨inferInstance, inferInstance⟩)).mem₀

/-- Compatible original Picard sections uniquely descend through the actual changed schemes. -/
theorem baseMarkedTranslation_sections_descend
    (s : ∀ j, (relativeFppfSheaf f).obj.obj (op (G j)))
    (hs : Presieve.Arrows.Compatible ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (fun j ↦ baseMarkedGluedChange f hL (b j) a) s) :
    ∃! t : (relativeFppfSheaf f).obj.obj (op (baseMarkedGluedTest f hL V a)),
      ∀ j, (relativeFppfSheaf f).obj.map (baseMarkedGluedChange f hL (b j) a).op t = s j := by
  have h := baseMarkedTranslation_isSheafFor f hL V a W b hb
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h s hs

/-- These local original sections recover the original glued section uniquely. -/
theorem baseMarkedTranslation_picard_unique
    (t : (relativeFppfSheaf f).obj.obj (op (baseMarkedGluedTest f hL V a)))
    (ht : ∀ j, (relativeFppfSheaf f).obj.map (baseMarkedGluedChange f hL (b j) a).op t =
      baseMarkedGluedPicard f hL (W j) (fun i ↦ baseMarkedIndexChange f (b j) (a i))) :
    t = baseMarkedGluedPicard f hL V a := by
  have h := baseMarkedTranslation_isSheafFor f hL V a W b hb
  apply h.isSeparatedFor.ext
  intro U k hk
  cases hk with
  | mk j => exact (ht j).trans (baseMarkedGluedChange_picard f hL (b j) a).symm

end FLT.Mazur.HilbertChart
