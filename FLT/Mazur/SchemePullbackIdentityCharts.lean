/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquareIdentity

/-!
# Unit charts on individual sheaves

Objectwise unit isomorphisms give explicit sheaf endpoints when transporting
reconstruction charts through an identity square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}}

/-- The unit chart with explicit source and target sheaves. -/
def identityChart (a : X ⟶ X) (ha : a = 𝟙 X) (A : X.Modules) :
    (pullback a).obj A ≅ A := (identityIso a ha).app A

/-- Identity reconstruction in the right-associated square convention. -/
theorem identity_chart (p : Y ⟶ X) (a : X ⟶ X) (b : Y ⟶ Y)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) (w : p ≫ a = b ≫ p)
    {A : X.Modules} {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    (((pullbackComp p a ≪≫ pullbackCongr w ≪≫ (pullbackComp b p).symm).app A ≪≫
        (pullback b).mapIso e).hom) ≫ (identityChart b hb M).hom =
      (pullback p).map (identityChart a ha A).hom ≫ e.hom := by
  simpa only [identityChart, squareIso, SheafPullbackPathComparison.comparison,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc] using
    reconstruction_identity p a b ha hb w e

end FLT.Mazur.SchemePullbackSquare
