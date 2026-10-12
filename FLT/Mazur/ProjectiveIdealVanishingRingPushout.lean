/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingPushout

/-!
# Vanishing coefficients for specified ring maps

This interface retains the actual four coordinate maps of an affine
cartesian square. All scalar actions and tower compatibilities are derived
from those maps and their pushout equation.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace FLT.Mazur.ProjectiveIdealVanishing
set_option backward.isDefEq.respectTransparency false
variable {R A B D : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing D]

/-- The coefficient ideal commutes with a pushout of the specified ring maps. -/
theorem ideal_ringPushout (r : R →+* A) (b : R →+* B) (a : A →+* D) (j : B →+* D)
    (H : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom b)
      (CommRingCat.ofHom a) (CommRingCat.ofHom j))
    (hB : let _ := b.toAlgebra; Module.Projective R B)
    (hD : let _ := a.toAlgebra; Module.Projective A D) (J : Ideal B) :
    (let _ := a.toAlgebra; let _ := hD; ideal A D (J.map j)) =
      (let _ := b.toAlgebra; let _ := hB; ideal R B J).map r := by
  let _ := r.toAlgebra
  let _ := b.toAlgebra
  let _ := a.toAlgebra
  let _ := j.toAlgebra
  let _ := (a.comp r).toAlgebra
  let _ : IsScalarTower R A D := .of_algebraMap_eq' rfl
  let _ : IsScalarTower R B D := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w)
  let _ : Algebra.IsPushout R A B D := CommRingCat.isPushout_iff_isPushout.mp H
  let _ := hB
  let _ := hD
  exact ideal_pushout R A B D J

end FLT.Mazur.ProjectiveIdealVanishing
