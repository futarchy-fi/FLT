/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackSectionSquare

/-!
# Named reconstruction along a section

Restrict a reconstruction around a square and retain a separately named
map to the original sheaf base. The comparison is derived from section
normalization and pullback associativity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' Z : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable (s : X' ⟶ Y') (hs : s ≫ q = 𝟙 X')
variable (t : X' ⟶ Y) (ht : s ≫ b = t) (ha : t ≫ p = a)

include ht in
/-- A section recovers the named original sheaf through the prescribed cover lift. -/
@[reassoc]
lemma named_reconstruction_section (c : Y ⟶ Z) (c' : Y' ⟶ Z)
    (hc : b ≫ c = c') (d : X' ⟶ Z) (hd : s ≫ c' = d) (hcd : t ≫ c = d)
    {A : X.Modules} {M : Z.Modules} (e : (pullback p).obj A ≅ (pullback c).obj M) :
    (pullback s).map
        (((squareIso p q a b w).app A ≪≫ (pullback b).mapIso e ≪≫
          (comparison b c c' hc).app M).hom) ≫
        (comparison s c' d hd).hom.app M =
      (retractIso s q hs ((pullback a).obj A)).hom ≫
        (comparison t p a ha).inv.app A ≫ (pullback t).map e.hom ≫
        (comparison t c d hcd).hom.app M := by
  have h := reconstruction_section p q a b w s hs t ht ha e
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] at h ⊢
  rw [comparison_assoc s b c t c' d ht hc hd hcd]
  exact h =≫ (comparison t c d hcd).hom.app M

end FLT.Mazur.SchemePullbackSquare
