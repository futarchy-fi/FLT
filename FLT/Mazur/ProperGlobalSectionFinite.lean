/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRingCohomologyFinite
public import FLT.Mazur.CoherentIdealIntersection
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Finite global functions over a Noetherian affine base

Proper coherent cohomology, in degree zero, makes the actual section ring a
finite module over the original base ring. In particular it is Noetherian, so
nil ideals in it have a uniform nilpotence exponent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperGlobalSectionFinite
open FCurve Chow.AffineBase
variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f]

/-- Actual global functions form a finite module for the original base scalar map. -/
lemma finite :
    let _ := (baseCohomologyScalars f).toAlgebra
    Module.Finite R Γ(X, ⊤) := by
  let _ := (baseCohomologyScalars f).toAlgebra
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  let _ := proper_coherent_hasFiniteRingCohomology f (structureModule X) 0
  let e : ModuleRingH (baseCohomologyScalars f) (structureModule X) 0 ≃ₗ[R]
      Γ(X, ⊤) :=
    { (moduleH0Equiv (structureModule X)).toAddEquiv with
      map_smul' := fun r a ↦ (moduleH0Equiv (structureModule X)).map_smul
        (baseCohomologyScalars f r) a }
  exact Module.Finite.equiv e

include f in
/-- The actual global section ring of a proper scheme over a Noetherian ring is Noetherian. -/
lemma isNoetherianRing : IsNoetherianRing Γ(X, ⊤) := by
  let _ := (baseCohomologyScalars f).toAlgebra
  let _ := finite f
  exact IsNoetherianRing.of_finite R Γ(X, ⊤)

include f in
/-- A nil ideal of actual proper global functions is nilpotent as an ideal. -/
lemma isNilpotent_of_le_nilradical (I : Ideal Γ(X, ⊤))
    (hI : I ≤ nilradical Γ(X, ⊤)) : IsNilpotent I := by
  let _ := isNoetherianRing f
  exact (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).mpr hI

end FLT.Mazur.ProperGlobalSectionFinite
