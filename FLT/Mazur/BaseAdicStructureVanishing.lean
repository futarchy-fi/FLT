/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologyReconstruction
public import FLT.Mazur.StructureIdealPowerCohomology

/-!
# Actual structure cohomology vanishing from closed thickenings

Proper cohomology over a complete noetherian base is reconstructed from its
adic tower. Vanishing on the actual closed schemes therefore implies
vanishing of the original cohomology, without identifying it by assumption
with completed cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.BaseAdicCohomology

open BaseAdicThickening Chow.AffineBase FCurve IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false

/-- Actual closed-thickening vanishing implies actual proper structure-cohomology vanishing. -/
theorem structureCohomology_subsingleton_of_thickenings
    {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}} [X.IsSeparated]
    (f : X ⟶ Spec R) [IsProper f] (J : Ideal R) [IsAdicComplete J R] (q : ℕ)
    (h : let _ := Chow.source_isNoetherian f
      ∀ n, Subsingleton (ModuleH
        (structureModule (((baseIdeal R J).comap f) ^ n).subscheme) q)) :
    Subsingleton (ModuleRingH (baseCohomologyScalars f) (structureModule X) q) := by
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  let I := (baseIdeal R J).comap f
  let ρ := baseCohomologyScalars f
  let _ : Subsingleton (compatibleCohomology ρ I (structureModule X) q) := by
    constructor
    intro x y
    apply Subtype.ext
    funext n
    let _ := h n
    let _ := StructureIdealPowerCohomology.quotient_subsingleton I ρ n q
    exact Subsingleton.elim _ _
  exact (cohomologyRestrictionEquiv f J (structureModule X) q).injective.subsingleton

end FLT.Mazur.BaseAdicCohomology
