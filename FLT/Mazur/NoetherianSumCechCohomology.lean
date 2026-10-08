/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianSumCechComplex
public import FLT.Mazur.AdditiveComplexSumHomology
public import FLT.Mazur.AffineCoverCohomology

/-!
# All-degree additive cohomology comparison for an original sheaf sum

A finite affine cover computes cohomology of quasi-coherent modules and their
sectionwise sum. The original complex and finite-support homology comparisons
identify the groups in every degree. Rees-action compatibility is a separate step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CechSheafHZero
open scoped DirectSum

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{0}} [TopologicalSpace.NoetherianSpace X]
  (M : ℕ → X.Modules) {ι : Type} [Fintype ι] (U : ι → X.Opens)

/-- The actual Cech cohomology of a sectionwise sum is the sum of original Cech cohomologies. -/
def cechCohomologyEquiv (q : ℕ) :
    CH U (moduleAbelianSheaf (sum M)) q ≃+
      ⨁ n, CH U (moduleAbelianSheaf (M n)) q :=
  (HomologicalComplex.homologyMapIso (cechSumIso M U).symm q).addCommGroupIsoToAddEquiv.trans
    (AdditiveComplexDirectSum.homologyEquiv (fun n ↦ C U (moduleAbelianSheaf (M n))) q)

variable [X.IsSeparated] [∀ n, (M n).IsQuasicoherent] [(sum M).IsQuasicoherent]
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- A finite affine cover gives the all-degree additive comparison for the original module sum. -/
def cohomologyEquiv (q : ℕ) : ModuleH (sum M) q ≃+ ⨁ n, ModuleH (M n) q :=
  (affineCoverCechEquiv (sum M) U hU hCover q).symm.toAddEquiv.trans
    ((cechCohomologyEquiv M U q).trans
      (DFinsupp.mapRange.addEquiv fun n ↦ (affineCoverCechEquiv (M n) U hU hCover q).toAddEquiv))

end FLT.Mazur.NoetherianModuleSum
