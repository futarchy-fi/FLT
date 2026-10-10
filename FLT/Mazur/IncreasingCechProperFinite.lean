/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCohomology
public import FLT.Mazur.ProperGlobalSectionFinite

/-!
# Finiteness of the actual bounded Cech cohomology

Proper coherent cohomology and the linear sorting comparison make every
cohomology module of the bounded affine-cover complex finite over the original
Noetherian base. The structure sheaf is a specialization, not an extra input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve Chow.AffineBase

variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [X.IsSeparated]
  (M : X.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover

/-- Every bounded Cech cohomology module of a proper coherent sheaf is finite. -/
theorem proper_cohomology_finite (n : ℕ) :
    let _ := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n)
      (baseCohomologyScalars f)
    Module.Finite R ((complex U (moduleAbelianSheaf M)).homology n) := by
  let _ := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n)
    (baseCohomologyScalars f)
  let _ := proper_coherent_hasFiniteRingCohomology f M n
  exact Module.Finite.equiv
    (affineRingCohomologyEquiv M U hU hCover (baseCohomologyScalars f) n).symm

omit M [M.IsFinitePresentation] [M.IsQuasicoherent] in
/-- Actual bounded structure cohomology is finite for every proper affine-base family. -/
theorem proper_structure_cohomology_finite (n : ℕ) :
    let _ := Module.compHom
      ((complex U (moduleAbelianSheaf (structureModule X))).homology n)
      (baseCohomologyScalars f)
    Module.Finite R ((complex U (moduleAbelianSheaf (structureModule X))).homology n) := by
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  exact proper_cohomology_finite f (structureModule X) U hU hCover n

end FLT.Mazur.IncreasingCechScalars
