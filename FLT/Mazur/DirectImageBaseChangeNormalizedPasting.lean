/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangePasting
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Pasting mates with specified composite maps

The actual mate for an independently specified outer square agrees with
the two successive mates, using the genuine pullback path comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.DirectImageBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {Q P X U T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (a : Q ⟶ P) (b : Q ⟶ U) (h : U ⟶ T)
  (v : b ≫ h = a ≫ q)

/-- Pasting retains the originally specified outer family and base map. -/
@[reassoc]
theorem comparison_paste_normalized (p' : Q ⟶ X) (g' : U ⟶ S)
    (wp : a ≫ p = p') (wg : h ≫ g = g') (w' : b ≫ g' = p' ≫ f)
    (M : X.Modules) :
    (pullback h).map (comparison p q f g w M) ≫
        comparison a b q h v ((pullback p).obj M) ≫
          (pushforward b).map
            ((SheafPullbackPathComparison.comparison a p p' wp).hom.app M) =
      (SheafPullbackPathComparison.comparison h g g' wg).hom.app
          ((pushforward f).obj M) ≫ comparison p' b f g' w' M := by
  subst p' g'
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr,
    Iso.trans_hom, Iso.refl_hom, NatTrans.comp_app, NatTrans.id_app,
    eqToIso_refl, Category.comp_id] using comparison_paste p q f g w a b h v M

end FLT.Mazur.DirectImageBaseChange
