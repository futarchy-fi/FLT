/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquareIdentity

/-!
# Composition coherence for pullback squares

Two consecutive scheme squares agree with their composite square after the
actual pullback composition charts on the base and cover.
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

include w v in
/-- Consecutive commutative squares compose. -/
theorem composite_square : r ≫ (c ≫ a) = (d ≫ b) ≫ p := by
  rw [← Category.assoc, v, Category.assoc, w, Category.assoc]

/-- Square comparisons compose using the actual pullback composition charts. -/
@[reassoc]
theorem squareIso_composition (A : X.Modules) :
    (pullback r).map ((pullbackComp c a).hom.app A) ≫
        (squareIso p r (c ≫ a) (d ≫ b) (composite_square p q r a b c d w v)).hom.app A =
      (squareIso q r c d v).hom.app ((pullback a).obj A) ≫
        (pullback d).map ((squareIso p q a b w).hom.app A) ≫
        (pullbackComp d b).hom.app ((pullback p).obj A) := by
  have hb : (d ≫ b) ≫ p = (d ≫ q) ≫ a := by
    rw [Category.assoc, ← w, ← Category.assoc]
  have hq : r ≫ (c ≫ a) = (d ≫ q) ≫ a := by rw [← Category.assoc, v]
  have hc (U V W : Scheme.{u}) (f : U ⟶ V) (g : V ⟶ W) :
      comparison f g (f ≫ g) rfl = pullbackComp f g := by
    simp only [comparison, pullbackCongr, eqToIso_refl, Iso.trans_refl]
  have hh := comparison_assoc r c a (d ≫ q) (c ≫ a) ((d ≫ q) ≫ a)
    v rfl hq rfl A
  rw [hc _ _ _ c a, hc _ _ _ (d ≫ q) a] at hh
  apply (cancel_mono ((comparison (d ≫ b) p ((d ≫ q) ≫ a) hb).hom.app A)).mp
  simp only [Category.assoc]
  rw [squareIso_comparison p r (c ≫ a) (d ≫ b) (composite_square p q r a b c d w v)
    ((d ≫ q) ≫ a) hq hb A, comparison_square p q a b w d (d ≫ q) rfl hb A]
  rw [← Category.assoc, squareIso_comparison q r c d v (d ≫ q) v rfl
    ((pullback a).obj A)]
  exact hh

/-- Reconstructed charts for two squares agree with the composite reconstructed chart. -/
@[reassoc]
theorem reconstruction_composition {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M) :
    (squareIso q r c d v).hom.app ((pullback a).obj A) ≫
        (pullback d).map ((squareIso p q a b w).hom.app A ≫ (pullback b).map e.hom) ≫
        (pullbackComp d b).hom.app M =
      (pullback r).map ((pullbackComp c a).hom.app A) ≫
        (squareIso p r (c ≫ a) (d ≫ b) (composite_square p q r a b c d w v)).hom.app A ≫
        (pullback (d ≫ b)).map e.hom := by
  have hn := (pullbackComp d b).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (pullback (d ≫ b)).map e.hom)
    (squareIso_composition p q r a b c d w v A).symm

end FLT.Mazur.SchemePullbackSquare
