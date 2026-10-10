/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechBaseComplex
public import FLT.Mazur.IncreasingCechFlatTerms

/-!
# Flat bounded structure terms over the original affine ring

The spectrum global-section isomorphism transports the already constructed
term flatness to the original ring. No flatness of cohomology is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open FCurve Chow.AffineBase

variable {R : CommRingCat.{0}} {X : Scheme.{0}}
  (f : X ⟶ Spec R) [Flat f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

include hU in
/-- Actual bounded structure terms are flat for the original affine-ring scalar action. -/
theorem baseStructureTerm_flat (n : ℕ) :
    Module.Flat R (BaseTerm (structureModule X) U (baseCohomologyScalars f) n) := by
  let A := Γ(Spec R, ⊤)
  let T := BaseTerm (structureModule X) U (baseCohomologyScalars f) n
  let _ : Algebra R A := (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  let _ : Module A T := Module.compHom
    ((IncreasingCechComplex.complex U (moduleAbelianSheaf (structureModule X))).X n)
    f.appTop.hom
  let _ : Module.Flat R A :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  let _ : Module.Flat A T := structureTerm_flat f U hU n
  let _ : IsScalarTower R A T := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact Module.Flat.trans R A T

end FLT.Mazur.IncreasingCechScalars
