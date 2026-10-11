/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChangeGeometry

/-!
# Actual covers of glued schemes induced by covers of the translation base

Every covering family on the given translation base produces a covering family
of the actual changed glued schemes. Coverage is proved from the scheme
pullback theorem, rather than postulated for translated charts.
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

/-- A jointly surjective family of base maps gives jointly surjective actual comparisons. -/
theorem baseMarkedGluedChanges_jointly_surjective
    (hb : ∀ x : V.left, ∃ j, ∃ y : (W j).left, (b j).left y = x)
    (x : (baseMarkedGluedTest f hL V a).left) :
    ∃ j, ∃ y : (baseMarkedGluedTest f hL (W j)
        (fun i ↦ baseMarkedIndexChange f (b j) (a i))).left,
      (baseMarkedGluedChange f hL (b j) a).left y = x := by
  obtain ⟨j, y, hy⟩ := hb ((baseMarkedGluedBase f hL V a).left x)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (baseMarkedGluedChange_isPullback f hL (b j) a) x y hy.symm
  exact ⟨j, z, hz⟩

/-- The actual changed glued schemes form a cover for every base-change-stable property. -/
def baseMarkedGluedChangeCover (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    (hb : ∀ x : V.left, ∃ j, ∃ y : (W j).left, (b j).left y = x)
    (hP : ∀ j, P (b j).left) :
    Scheme.Cover (Scheme.precoverage P) (baseMarkedGluedTest f hL V a).left where
  I₀ := κ
  X j := (baseMarkedGluedTest f hL (W j)
    (fun i ↦ baseMarkedIndexChange f (b j) (a i))).left
  f j := (baseMarkedGluedChange f hL (b j) a).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨baseMarkedGluedChanges_jointly_surjective f hL V a W b hb,
      fun j ↦ baseMarkedGluedChange_property f hL (b j) a P (hP j)⟩

/-- The original Picard class is preserved on every member of the induced cover. -/
theorem baseMarkedGluedChangeCover_picard (j : κ) :
    (relativeFppfSheaf f).obj.map (baseMarkedGluedChange f hL (b j) a).op
        (baseMarkedGluedPicard f hL V a) =
      baseMarkedGluedPicard f hL (W j) (fun i ↦ baseMarkedIndexChange f (b j) (a i)) :=
  baseMarkedGluedChange_picard f hL (b j) a

/-- An open cover of the actual translation base gives open charts by the changed schemes. -/
def baseMarkedGluedTranslationOpenCover (C : V.left.OpenCover) :
    (baseMarkedGluedTest f hL V a).left.OpenCover :=
  baseMarkedGluedChangeCover f hL V a (fun j ↦ Over.mk (C.f j ≫ V.hom))
    (fun j ↦ Over.homMk (C.f j)) _ (fun x ↦ C.exists_eq x)
    (fun j ↦ (show IsOpenImmersion (C.f j) from inferInstance))

end FLT.Mazur.HilbertChart
