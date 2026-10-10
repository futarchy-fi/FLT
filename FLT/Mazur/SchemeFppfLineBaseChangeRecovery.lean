/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfLineBaseChange

/-!
# Base change retains the original source recovery

Pulling the gluing comparison back to the covering scheme gives precisely
refinement of the chosen source recovery, preceded by the actual square chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable [Flat q] [Surjective q] [LocallyOfFinitePresentation q]

/-- The actual base-change comparison intertwines the prescribed source recoveries. -/
@[reassoc]
lemma lineGluingRefine_sourceRecovery (D : LineData p) :
    (lineCanonical q).map ((lineGluingRefine p q a b w).hom.app D) ≫
        (lineSourceRecovery q).hom.app ((lineRefine p q a b w).obj D) =
      (lineCanonicalRefine p q a b w).hom.app ((lineGluing p).obj D) ≫
        (lineRefine p q a b w).map ((lineSourceRecovery p).hom.app D) := by
  let k := (lineCanonicalRefine p q a b w).hom.app ((lineGluing p).obj D) ≫
    (lineRefine p q a b w).map ((lineSourceRecovery p).hom.app D)
  have h := (lineSourceRecovery q).hom.naturality k
  change (lineCanonical q).map ((lineGluing q).map k) ≫
    (lineSourceRecovery q).hom.app ((lineRefine p q a b w).obj D) =
    (lineSourceRecovery q).hom.app
      ((lineCanonical q).obj ((lineBundlePullback a).obj ((lineGluing p).obj D))) ≫ k at h
  rw [lineGluingRefine_hom, ← Functor.map_comp]
  change (lineCanonical q).map
    ((lineBaseRecovery q).hom.app ((lineBundlePullback a).obj ((lineGluing p).obj D)) ≫
      (lineGluing q).map k) ≫ _ = k
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc,
    lineBaseRecovery_triangle]
  exact Category.id_comp k

end FLT.Mazur.SchemeAffineDescent
