/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackIdentityCharts

/-!
# Explicit reconstruction charts for scheme squares

The source is written as two successive pullbacks, keeping object comparisons
small when the square is specialized to affine schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}

/-- Transport a reconstruction with explicit iterated-pullback endpoints. -/
def reconstructionChart (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (w : q ≫ a = b ≫ p) {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M) :
    (pullback q).obj ((pullback a).obj A) ≅ (pullback b).obj M :=
  (pullbackComp q a ≪≫ pullbackCongr w ≪≫ (pullbackComp b p).symm).app A ≪≫
    (pullback b).mapIso e

/-- Transport around an identity square respects the objectwise unit charts. -/
theorem reconstructionChart_identity (p : Y ⟶ X) (a : X ⟶ X) (b : Y ⟶ Y)
    (ha : a = 𝟙 X) (hb : b = 𝟙 Y) (w : p ≫ a = b ≫ p)
    {A : X.Modules} {M : Y.Modules} (e : (pullback p).obj A ≅ M) :
    (reconstructionChart p p a b w e).hom ≫ (identityChart b hb M).hom =
      (pullback p).map (identityChart a ha A).hom ≫ e.hom :=
  identity_chart p a b ha hb w e

end FLT.Mazur.SchemePullbackSquare
