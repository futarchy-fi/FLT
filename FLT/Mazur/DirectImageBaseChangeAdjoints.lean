/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeMate
public import FLT.Mazur.TwistedSectionPushforward

/-!
# Adjoint normalization of base-changed direct-image maps

Pulling a map into a direct image and composing with the actual base-change
mate pulls its counit adjoint through the geometric square. Specializing to
a twisted section retains the canonical dual-line pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.DirectImageBaseChange
open FCurve SchemePullbackSquare ModuleSheafTensor
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f)

/-- Base change of a direct-image map pulls its actual counit adjoint. -/
lemma comparison_map_adjoint {A : S.Modules} {L : X.Modules}
    (a : A ⟶ (pushforward f).obj L) :
    ((pullbackPushforwardAdjunction q).homEquiv _ _).symm
        ((pullback g).map a ≫ comparison p q f g w L) =
      (squareIso f q g p w).hom.app A ≫
        (pullback p).map (((pullbackPushforwardAdjunction f).homEquiv _ _).symm a) := by
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [comparison, Equiv.symm_apply_apply]
  rw [← Category.assoc]
  erw [(squareIso f q g p w).hom.naturality]
  rw [Category.assoc, Functor.comp_map, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Equality with the base-changed map can be tested on total-space adjoints. -/
lemma eq_comparison_map_iff {A : S.Modules} {L : X.Modules}
    (a : A ⟶ (pushforward f).obj L)
    (b : (pullback g).obj A ⟶ (pushforward q).obj ((pullback p).obj L)) :
    b = (pullback g).map a ≫ comparison p q f g w L ↔
      ((pullbackPushforwardAdjunction q).homEquiv _ _).symm b =
        (squareIso f q g p w).hom.app A ≫
          (pullback p).map (((pullbackPushforwardAdjunction f).homEquiv _ _).symm a) := by
  rw [← comparison_map_adjoint]
  exact ((pullbackPushforwardAdjunction q).homEquiv _ _).symm.injective.eq_iff.symm

/-- For twisted sections the normalized pulled adjoint uses the original dual comparison. -/
lemma twistedSection_comparison_adjoint (L : X.Modules) {B : S.Modules}
    (hB : LocallyFreeRankOne B) (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    ((pullbackPushforwardAdjunction q).homEquiv _ _).symm
        ((pullback g).map (twistedSectionPushforwardEquiv f L hB s) ≫
          comparison p q f g w L) =
      (squareIso f q g p w).hom.app (moduleSheafDual B) ≫
        (pullback p).map ((moduleSheafDualPullbackIso f hB).hom ≫
          (lineHomSectionEquiv L (hB.pullback f)).symm s) := by
  rw [comparison_map_adjoint, twistedSectionPushforwardEquiv_adjoint]

end FLT.Mazur.DirectImageBaseChange
