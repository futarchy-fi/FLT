/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StructureIdealPowerQuotient
public import FLT.Mazur.ClosedPushforwardCohomology

/-!
# Actual closed-thickening cohomology of adic structure quotients

The structure quotient comparison and closed direct image identify adic
coefficient cohomology with the actual closed thickening's cohomology,
retaining the original base-ring action in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.StructureIdealPowerCohomology

open FCurve

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
  (I : X.IdealSheafData) {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- Adic structure-quotient cohomology is actual closed-thickening cohomology over the base. -/
def quotientEquiv (n q : ℕ) :
    ModuleRingH ρ (IdealAdicQuotient.quotient I (structureModule X) n) q ≃ₗ[R]
      ModuleRingH ((I ^ n).subschemeι.appTop.hom.comp ρ)
        (structureModule (I ^ n).subscheme) q := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (I ^ n).subschemeι
  let _ := CoherentIdealIntersection.structureModule_coherent (X := (I ^ n).subscheme)
  exact ((moduleRingHFunctor ρ q).mapIso
    (StructureIdealPowerQuotient.quotientIso I n)).toLinearEquiv.trans
      (closedPushforwardRingHEquiv (I ^ n).subschemeι
        (structureModule (I ^ n).subscheme) ρ q)

/-- Vanishing on the actual closed thickening gives vanishing for the original adic quotient. -/
theorem quotient_subsingleton (n q : ℕ)
    [Subsingleton (ModuleH (structureModule (I ^ n).subscheme) q)] :
    Subsingleton (ModuleRingH ρ (IdealAdicQuotient.quotient I (structureModule X) n) q) := by
  constructor
  intro x y
  apply (quotientEquiv I ρ n q).injective
  exact Subsingleton.elim (α := ModuleH (structureModule (I ^ n).subscheme) q) _ _

end FLT.Mazur.StructureIdealPowerCohomology
