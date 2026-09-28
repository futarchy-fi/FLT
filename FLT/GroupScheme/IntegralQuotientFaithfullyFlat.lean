/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualFaithfullyFlat
public import FLT.GroupScheme.RaynaudFlatKernelExactness
public import FLT.GroupScheme.RaynaudQuotientFiberFreeness

/-!
# Faithfully flat contracted quotients over principal ideal domains

The contracted quotient inclusion remains injective on every residue fibre.
The finite Hopf freeness criterion therefore proves relative faithful flatness
over any principal ideal domain, in particular over `ZInvTwo`. The actual
kernel is consequently the flat closure of the prescribed generic kernel.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    [IsPrincipalIdealRing R] {S X Y : FF R K}

/-- A contracted generic quotient is faithfully flat over a principal ideal domain. -/
theorem GenericGaloisHom.quotientCoordinatesFaithfullyFlat
    (q : GenericGaloisHom X Y) :
    Module.FaithfullyFlat q.quotientCoordinates X.CoordinateRing :=
  HopfAlgebra.faithfullyFlat_of_injective_residueBaseChange q.quotientInclusion
    (by ext; rfl) Subtype.val_injective
    (fun I _ ↦ q.quotientInclusion_baseChange_injective (R ⧸ I))

/-- Over a principal ideal domain the contracted quotient's kernel equations are
exactly those of the flat closure of its generic kernel. -/
theorem GenericGaloisHom.quotientKernelIdealEqClosureIdeal
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) :
    q.quotientKernelIdeal = i.closureIdeal := by
  letI quotientFlat : Module.FaithfullyFlat q.quotientCoordinates X.CoordinateRing :=
    q.quotientCoordinatesFaithfullyFlat
  exact i.quotientKernelIdeal_eq_closureIdeal_of_relative_flat q hq hexact

end ThreeAdicPlan
