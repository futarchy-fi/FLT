/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackSquarePasting
public import FLT.Mazur.DirectImageBaseChangeAdjoints

/-!
# Composition of actual direct-image base-change mates

Pasting two commutative squares composes their independently defined mates.
The equality retains the canonical source and coefficient pullback comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.DirectImageBaseChange
open SchemePullbackSquare
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Q P X U T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (a : Q ⟶ P) (b : Q ⟶ U) (h : U ⟶ T)
  (v : b ≫ h = a ≫ q)

/-- The actual comparison for a pasted square is the composite of the two mates. -/
@[reassoc]
theorem comparison_paste (M : X.Modules) :
    (pullback h).map (comparison p q f g w M) ≫
        comparison a b q h v ((pullback p).obj M) ≫
          (pushforward b).map ((pullbackComp a p).hom.app M) =
      (pullbackComp h g).hom.app ((pushforward f).obj M) ≫
        comparison (a ≫ p) b f (h ≫ g) (paste_eq p q f g w a b h v) M := by
  apply ((pullbackPushforwardAdjunction b).homEquiv _ _).symm.injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    comparison_map_adjoint, Adjunction.homEquiv_naturality_left_symm]
  simp only [comparison, Equiv.symm_apply_apply, Functor.map_comp, Category.assoc]
  rw [squareIso_paste_assoc p q f g w a b h v]
  rw [← (pullbackComp a p).hom.naturality]
  rfl

end FLT.Mazur.DirectImageBaseChange
