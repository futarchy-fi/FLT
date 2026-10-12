/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointDivisorIsoCohomology

/-!
# Field cohomology on an independently specified family square

The canonical fiber product and any specified cartesian total space have
linearly equivalent cohomology of the original pulled coefficient. The
comparison retains the given field structure map, including its scalars.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {P X S : Scheme}
  {p : P ⟶ X} {q : P ⟶ Spec (.of k)} {f : X ⟶ S} {g : Spec (.of k) ⟶ S}
  (h : IsPullback p q f g) (L : X.Modules) (n : ℕ)

/-- Cartesian identification preserves the actual field-linear cohomology. -/
def cartesianLineScalarHIso :
    ModuleScalarH (pullback.snd f g) ((Scheme.Modules.pullback (pullback.fst f g)).obj L) n
      ≃ₗ[k] ModuleScalarH q ((Scheme.Modules.pullback p).obj L) n := by
  let a := (Scheme.Modules.pullback (pullback.fst f g)).obj L
  have e := moduleScalarHPullbackIsoEquiv h.isoPullback (pullback.snd f g) a n
  rw [h.isoPullback_hom_snd] at e
  let b := (pullbackComp h.isoPullback.hom (pullback.fst f g)).app L ≪≫
    (pullbackCongr h.isoPullback_hom_fst).app L
  exact e.trans (((moduleScalarHFunctor q n).mapIso b).toLinearEquiv)

include h

/-- Vanishing is independent of the chosen cartesian total space. -/
theorem cartesianLine_vanishing_iff :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst f g)).obj L) n) ↔
      Subsingleton (ModuleH ((Scheme.Modules.pullback p).obj L) n) :=
  Equiv.subsingleton_congr (cartesianLineScalarHIso h L n).toEquiv

/-- Section dimensions use the original field action on either family square. -/
theorem cartesianLine_finrank :
    Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj L) n) =
      Module.finrank k (ModuleScalarH (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj L) n) :=
  (cartesianLineScalarHIso h L n).finrank_eq.symm

end FLT.Mazur.FCurve
