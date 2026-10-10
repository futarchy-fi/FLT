/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Diagonal laws under an isomorphism of source modules

An isomorphism intertwining two overlap maps transfers their diagonal law.
This allows independently supplied member modules to recover the law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapDiagonalChart
open SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z : Scheme.{u}} (l r : Z ⟶ Y) (d : Y ⟶ Z)
variable (hl : d ≫ l = 𝟙 Y) (hr : d ≫ r = 𝟙 Y)

/-- The retraction comparison is natural in the original module. -/
@[reassoc]
lemma retractIso_naturality {M N : Y.Modules} (f : M ⟶ N) :
    (pullback d).map ((pullback l).map f) ≫ (retractIso d l hl N).hom =
      (retractIso d l hl M).hom ≫ f :=
  (pullbackComp d l ≪≫ pullbackCongr hl ≪≫ pullbackId Y).hom.naturality f

/-- An intertwining source isomorphism detects the diagonal identity. -/
lemma diagonal_of_sourceIso {M N : Y.Modules} (i : M ≅ N)
    (e : (pullback l).obj M ≅ (pullback r).obj M)
    (e' : (pullback l).obj N ≅ (pullback r).obj N)
    (h : e.hom ≫ (pullback r).map i.hom = (pullback l).map i.hom ≫ e'.hom)
    (he : DiagonalCompatible l r d hl hr N e') :
    DiagonalCompatible l r d hl hr M e := by
  unfold DiagonalCompatible at he ⊢
  apply (cancel_mono i.hom).mp
  simp only [Category.assoc]
  rw [← retractIso_naturality r d hr, ← Functor.map_comp_assoc, h,
    Functor.map_comp, Category.assoc, he, retractIso_naturality l d hl]

end FLT.Mazur.SchemeOverlapDiagonalChart
