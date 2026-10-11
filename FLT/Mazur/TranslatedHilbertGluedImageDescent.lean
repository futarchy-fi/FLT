/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedDescent

/-!
# Fppf descent of arbitrary maps into the glued Picard image

Local representatives may already range across several translated charts.
The proved monicity makes them compatible, and subcanonicity descends the
actual maps. Thus membership in the image is fppf local on every test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)

/-- Arbitrary fppf-local representatives descend uniquely to the same glued scheme. -/
theorem translatedHilbertGluedPoint_of_fppf_image
    (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
    {κ : Type} (V : κ → Over (Spec (.of R))) (c : ∀ i, V i ⟶ T)
    (hc : Sieve.ofArrows V c ∈ (Scheme.fppfTopology.over (Spec (.of R))) T)
    (p : ∀ i, V i ⟶ translatedHilbertGluedTest f hL a)
    (hp : ∀ i, translatedHilbertGluedPoint f hL a (V i) (p i) =
      (relativeFppfSheaf f).obj.map (c i).op s) :
    ∃! k : T ⟶ translatedHilbertGluedTest f hL a,
      translatedHilbertGluedPoint f hL a T k = s := by
  have hcompat : Presieve.Arrows.Compatible
      (yoneda.obj (translatedHilbertGluedTest f hL a)) c p := by
    intro i j W b d he
    apply translatedHilbertGluedPoint_injective f hL a W
    change translatedHilbertGluedPoint f hL a W (b ≫ p i) =
      translatedHilbertGluedPoint f hL a W (d ≫ p j)
    rw [translatedHilbertGluedPoint_natural, translatedHilbertGluedPoint_natural, hp, hp]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg (fun z ↦ (relativeFppfSheaf f).obj.map z.op s) he
  have hy : Presieve.IsSheafFor (yoneda.obj (translatedHilbertGluedTest f hL a))
      (Presieve.ofArrows V c) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology.over (Spec (.of R))) _).isSheafFor _ hc
  obtain ⟨k, hk, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hy p hcompat
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  have hpic : Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows V c) := hs.isSheafFor _ hc
  have hks : translatedHilbertGluedPoint f hL a T k = s := by
    apply hpic.isSeparatedFor.ext
    rintro W b ⟨i⟩
    change (relativeFppfSheaf f).obj.map (c i).op (translatedHilbertGluedPoint f hL a T k) = _
    rw [← translatedHilbertGluedPoint_natural, show c i ≫ k = p i from hk i, hp]
    rfl
  exact ⟨k, hks, fun l hl ↦ translatedHilbertGluedPoint_injective f hL a T (hl.trans hks.symm)⟩

end FLT.Mazur.HilbertChart
