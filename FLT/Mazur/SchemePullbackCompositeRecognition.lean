/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackCompositeCharts

/-!
# Recognition of composite charts

Transport composition coherence along equalities of named charts before
specializing to concrete schemes. This keeps affine equality transport small.
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

/-- Recognize composition for independently named square comparisons. -/
theorem squareIso_composition_of_eq (A : X.Modules)
    (I : pullback a ⋙ pullback q ≅ pullback p ⋙ pullback b)
    (J : pullback c ⋙ pullback r ≅ pullback q ⋙ pullback d)
    (K : pullback ac ⋙ pullback r ≅ pullback p ⋙ pullback bd)
    (hI : I = squareIso p q a b w) (hJ : J = squareIso q r c d v)
    (hK : K = squareIso p r ac bd wv) :
    (pullback r).map ((comparison c a ac ha).hom.app A) ≫ K.hom.app A =
      J.hom.app ((pullback a).obj A) ≫ (pullback d).map (I.hom.app A) ≫
        (comparison d b bd hb).hom.app ((pullback p).obj A) := by
  rw [hI, hJ, hK]
  exact squareIso_composite_charts p q r a b c d w v ac bd ha hb wv A

/-- Recognize composition for independently named reconstruction charts. -/
theorem reconstruction_composition_of_eq {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M)
    (E : (pullback q).obj ((pullback a).obj A) ≅ (pullback b).obj M)
    (F : (pullback r).obj ((pullback c).obj ((pullback a).obj A)) ≅
      (pullback d).obj ((pullback b).obj M))
    (G : (pullback r).obj ((pullback ac).obj A) ≅ (pullback bd).obj M)
    (hE : E = reconstructionChart p q a b w e)
    (hF : F = reconstructionChart q r c d v E)
    (hG : G = reconstructionChart p r ac bd wv e) :
    F.hom ≫ (comparison d b bd hb).hom.app M =
      (pullback r).map ((comparison c a ac ha).hom.app A) ≫ G.hom := by
  rw [hF, hE, hG]
  exact reconstructionChart_composition p q r a b c d w v ac bd ha hb wv e

end FLT.Mazur.SchemePullbackSquare
