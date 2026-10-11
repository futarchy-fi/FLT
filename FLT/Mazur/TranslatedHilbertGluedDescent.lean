/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertGluedMono
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Fppf descent of translated Hilbert presentations

A section locally represented by the chosen translated charts has a unique
global map to their actual glued scheme. Coverage by enough charts remains a
separate geometric input, rather than a field of the constructed scheme.
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

/-- Fppf-local chart presentations descend to one actual map to the glued scheme. -/
theorem translatedHilbertGluedPoint_of_fppf_charts
    (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
    {κ : Type} (V : κ → Over (Spec (.of R))) (c : ∀ i, V i ⟶ T)
    (hc : Sieve.ofArrows V c ∈ (Scheme.fppfTopology.over (Spec (.of R))) T)
    (j : κ → ι) (p : ∀ i, V i ⟶ acyclicHilbertTest f (a (j i)).1)
    (hp : ∀ i, translatedHilbertPicardPoint f (a (j i)).1 hL (a (j i)).2 (V i) (p i) =
      (relativeFppfSheaf f).obj.map (c i).op s) :
    ∃! k : T ⟶ translatedHilbertGluedTest f hL a,
      translatedHilbertGluedPoint f hL a T k = s := by
  let q i := p i ≫ translatedHilbertGluedArrow f hL a (j i)
  have hq i : translatedHilbertGluedPoint f hL a (V i) (q i) =
      (relativeFppfSheaf f).obj.map (c i).op s := by
    rw [translatedHilbertGluedPoint_chart]
    exact hp i
  have hcompat : Presieve.Arrows.Compatible
      (yoneda.obj (translatedHilbertGluedTest f hL a)) c q := by
    intro i j W b d he
    apply translatedHilbertGluedPoint_injective f hL a W
    change translatedHilbertGluedPoint f hL a W (b ≫ q i) =
      translatedHilbertGluedPoint f hL a W (d ≫ q j)
    rw [translatedHilbertGluedPoint_natural f hL a b (q i),
      translatedHilbertGluedPoint_natural f hL a d (q j), hq, hq]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg (fun z ↦ (relativeFppfSheaf f).obj.map z.op s) he
  have hy : Presieve.IsSheafFor (yoneda.obj (translatedHilbertGluedTest f hL a))
      (Presieve.ofArrows V c) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology.over (Spec (.of R))) _).isSheafFor _ hc
  obtain ⟨k, hk, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hy q hcompat
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  have hpic : Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows V c) := hs.isSheafFor _ hc
  have hks : translatedHilbertGluedPoint f hL a T k = s := by
    apply hpic.isSeparatedFor.ext
    rintro W b ⟨i⟩
    change (relativeFppfSheaf f).obj.map (c i).op
      (translatedHilbertGluedPoint f hL a T k) = _
    rw [← translatedHilbertGluedPoint_natural]
    rw [show c i ≫ k = q i from hk i, hq]
    rfl
  exact ⟨k, hks, fun l hl ↦ translatedHilbertGluedPoint_injective f hL a T (hl.trans hks.symm)⟩

end FLT.Mazur.HilbertChart
