/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquareComposition
public import FLT.Mazur.SchemeRefinementReconstruction

/-!
# Composition charts with specified composite endpoints

The composite maps may be named independently of categorical composition.
This includes the spectrum of a composite ring map and its equality transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' X'' Y'' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (r : Y'' ⟶ X'')
variable (a : X' ⟶ X) (b : Y' ⟶ Y) (c : X'' ⟶ X') (d : Y'' ⟶ Y')
variable (w : q ≫ a = b ≫ p) (v : r ≫ c = d ≫ q)
variable (ac : X'' ⟶ X) (bd : Y'' ⟶ Y)
variable (ha : c ≫ a = ac) (hb : d ≫ b = bd) (wv : r ≫ ac = bd ≫ p)

/-- Square composition includes transport to the specified composite maps. -/
@[reassoc]
theorem squareIso_composite_charts (A : X.Modules) :
    (pullback r).map ((comparison c a ac ha).hom.app A) ≫
        (squareIso p r ac bd wv).hom.app A =
      (squareIso q r c d v).hom.app ((pullback a).obj A) ≫
        (pullback d).map ((squareIso p q a b w).hom.app A) ≫
        (comparison d b bd hb).hom.app ((pullback p).obj A) := by
  subst ac bd
  simpa only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl] using
    squareIso_composition p q r a b c d w v A

/-- Successive reconstruction agrees with reconstruction along the composite square. -/
@[reassoc]
theorem reconstructionChart_composition {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M) :
    (reconstructionChart q r c d v (reconstructionChart p q a b w e)).hom ≫
        (comparison d b bd hb).hom.app M =
      (pullback r).map ((comparison c a ac ha).hom.app A) ≫
        (reconstructionChart p r ac bd wv e).hom := by
  subst ac bd
  simpa only [reconstructionChart, comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Iso.symm_hom, squareIso, Category.assoc] using
    reconstruction_composition p q r a b c d w v e

end FLT.Mazur.SchemePullbackSquare
