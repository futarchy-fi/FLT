/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisModuleMorphism

/-!
# Extending structure-linear affine isomorphisms

An affine-basis isomorphism whose forward maps preserve the original scalars
extends to an isomorphism of the original module sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineBasisModuleMorphism

variable {X : Scheme.{u}} (M N : X.Modules) (e : basis M ≅ basis N)
  (he : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
    e.hom.hom.app (.op U) (r • s) = r •
      (show Γ(N, U.1) from e.hom.hom.app (.op U) s))

/-- The original affine component, with its module-section types explicit. -/
def componentIso (U : X.affineOpens) : Γ(M, U.1) ≅ Γ(N, U.1) :=
  ((sheafToPresheaf _ _).mapIso e).app (.op U)

include he in
/-- The inverse affine maps also preserve the original scalars. -/
lemma inverse_linear (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(N, U.1)) :
    e.inv.hom.app (.op U) (r • s) = r •
      (show Γ(M, U.1) from e.inv.hom.app (.op U) s) := by
  change (componentIso M N e U).inv (r • s) = r • (componentIso M N e U).inv s
  apply (ConcreteCategory.bijective_of_isIso (componentIso M N e U).hom).injective
  rw [Iso.inv_hom_id_apply]
  change r • s = e.hom.hom.app (.op U)
    (r • (show Γ(M, U.1) from e.inv.hom.app (.op U) s))
  rw [he]
  change r • s = r • ((componentIso M N e U).hom ((componentIso M N e U).inv s))
  rw [Iso.inv_hom_id_apply]

/-- Extend the given affine isomorphism without changing either module sheaf. -/
def extendIso : M ≅ N where
  hom := extend M N e.hom he
  inv := extend N M e.inv (inverse_linear M N e he)
  hom_inv_id := by
    apply hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro s
    change (extend N M e.inv (inverse_linear M N e he)).app U.1
      ((extend M N e.hom he).app U.1 s) = s
    rw [extend_app, extend_app]
    exact (componentIso M N e U).hom_inv_id_apply s
  inv_hom_id := by
    apply hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro s
    change (extend M N e.hom he).app U.1
      ((extend N M e.inv (inverse_linear M N e he)).app U.1 s) = s
    rw [extend_app, extend_app]
    exact (componentIso M N e U).inv_hom_id_apply s

/-- The global extension retains the supplied forward affine coordinates. -/
lemma extendIso_hom_app (U : X.affineOpens) :
    (extendIso M N e he).hom.app U.1 = e.hom.hom.app (.op U) :=
  extend_app M N e.hom he U

/-- The global extension retains the supplied inverse affine coordinates. -/
lemma extendIso_inv_app (U : X.affineOpens) :
    (extendIso M N e he).inv.app U.1 = e.inv.hom.app (.op U) :=
  extend_app N M e.inv (inverse_linear M N e he) U

end FLT.Mazur.AffineBasisModuleMorphism
