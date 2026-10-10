/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback

/-!
# Recovering ample opens through an affine morphism

An ample open of the extending line pulls back to an ample open of the
specified original line. The comparison uses the actual restriction square
and the given sheaf isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

universe u

/-- An ample restriction recovers along an affine map and a specified line isomorphism. -/
theorem ampleLineBundle_open_affine_recovery {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsAffineHom i] (M : Y.Modules) (L : X.Modules) (e : (pullback i).obj M ≅ L)
    (U : Y.Opens) (hA : AmpleLineBundle ((pullback U.ι).obj M)) :
    AmpleLineBundle ((pullback (i ⁻¹ᵁ U).ι).obj L) := by
  let _ : IsAffineHom (i ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i U).flip
      (inferInstanceAs (IsAffineHom i))
  have ha := hA.pullback_affine (i ∣_ U)
  apply ha.of_iso
  exact (pullback (i ⁻¹ᵁ U).ι).mapIso e.symm ≪≫
    (pullbackComp (i ⁻¹ᵁ U).ι i).app M ≪≫
    (pullbackCongr (morphismRestrict_ι i U).symm).app M ≪≫
    ((pullbackComp (i ∣_ U) U.ι).app M).symm

end FLT.Mazur.FCurve
