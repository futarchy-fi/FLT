/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherent comparisons for paths of scheme pullbacks

Normalize an iterated pullback using a specified equality of scheme maps.
Associativity and both unit laws follow from the sheaf pullback pseudofunctor.
These comparisons allow overlap equations to be transported between charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {W X Y Z : Scheme.{u}}

/-- Normalize a two-step pullback along a specified composite scheme map. -/
def comparison (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k) :
    pullback g ⋙ pullback f ≅ pullback k :=
  pullbackComp f g ≪≫ pullbackCongr w

/-- The associativity comparison evaluated at a sheaf. -/
@[reassoc]
theorem comp_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (M : Z.Modules) :
    (pullback f).map ((pullbackComp g h).hom.app M) ≫
      (pullbackComp f (g ≫ h)).hom.app M ≫
      (pullbackCongr (Category.assoc f g h).symm).hom.app M =
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫
      (pullbackComp (f ≫ g) h).hom.app M := by
  have hh := NatTrans.congr_app (pseudofunctor_associativity f g h) M
  dsimp at hh
  apply (cancel_epi ((pullback f).map ((pullbackComp g h).inv.app M))).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  apply (cancel_epi ((pullbackComp f (g ≫ h)).inv.app M)).mp
  simpa [pullbackCongr] using hh.symm

/-- Every normalization of a three-step path has the same comparison. -/
@[reassoc]
theorem comparison_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (k : W ⟶ Z)
    (wfg : f ≫ g = fg) (wgh : g ≫ h = gh)
    (wl : f ≫ gh = k) (wr : fg ≫ h = k) (M : Z.Modules) :
    (pullback f).map ((comparison g h gh wgh).hom.app M) ≫
      (comparison f gh k wl).hom.app M =
    (comparison f g fg wfg).hom.app ((pullback h).obj M) ≫
      (comparison fg h k wr).hom.app M := by
  subst fg gh k
  simpa [comparison, pullbackCongr] using comp_assoc f g h M

/-- Normalizing a path ending in an identity is the pulled-back identity comparison. -/
@[reassoc]
theorem comparison_comp_id (f : X ⟶ Y) (M : Y.Modules) :
    (comparison f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (pullback f).map ((pullbackId Y).hom.app M) := by
  have hh := NatTrans.congr_app (pseudofunctor_left_unitality f) M
  dsimp at hh
  apply (cancel_epi ((pullbackComp f (𝟙 Y)).inv.app M)).mp
  simpa [comparison, pullbackCongr] using hh.symm

/-- Normalizing a path starting in an identity is the identity comparison on the pullback. -/
@[reassoc]
theorem comparison_id_comp (f : X ⟶ Y) (M : Y.Modules) :
    (comparison (𝟙 X) f f (Category.id_comp f)).hom.app M =
      (pullbackId X).hom.app ((pullback f).obj M) := by
  have hh := NatTrans.congr_app (pseudofunctor_right_unitality f) M
  dsimp at hh
  apply (cancel_epi ((pullbackComp (𝟙 X) f).inv.app M)).mp
  simpa [comparison, pullbackCongr] using hh.symm

end FLT.Mazur.SheafPullbackPathComparison
