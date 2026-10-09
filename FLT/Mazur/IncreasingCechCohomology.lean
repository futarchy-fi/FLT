/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechScalars
public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.ModuleCohomologyRing
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Linear cohomology comparison for bounded Cech complexes

Transporting the scalar action through sorting agrees with the actual action
of coefficient multiplication. The bounded complex therefore computes
cohomology linearly over global sections and over any original base ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex CechSortingMaps CechSortingHomotopy FCurve CechSheafHZero

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

/-- The scalar action transported through the proved sorting comparison. -/
instance homologyModule (n : ℕ) :
    Module Γ(X, ⊤) ((complex U (moduleAbelianSheaf M)).homology n) :=
  (homologyEquiv U (moduleAbelianSheaf M) n).symm.module Γ(X, ⊤)

/-- Sorting induces a linear cohomology equivalence. -/
def linearHomologyEquiv (n : ℕ) :
    CH U (moduleAbelianSheaf M) n ≃ₗ[Γ(X, ⊤)]
      (complex U (moduleAbelianSheaf M)).homology n :=
  ((homologyEquiv U (moduleAbelianSheaf M) n).symm.linearEquiv Γ(X, ⊤)).symm

/-- The transported action is precisely actual coefficient multiplication on homology. -/
lemma homology_smul (n : ℕ) (r : Γ(X, ⊤))
    (x : (complex U (moduleAbelianSheaf M)).homology n) :
    r • x = HomologicalComplex.homologyMap (coefficientMap U (moduleMultiply M r)) n x := by
  obtain ⟨y, rfl⟩ := (linearHomologyEquiv M U n).surjective x
  rw [← (linearHomologyEquiv M U n).map_smul]
  exact ConcreteCategory.congr_hom
    (homologyIso_naturality U (moduleAbelianSheaf M) (moduleMultiply M r) n) y

variable [X.IsSeparated] [M.IsQuasicoherent]
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- The actual bounded complex of an affine cover computes sheaf cohomology linearly. -/
def affineCohomologyEquiv (n : ℕ) :
    (complex U (moduleAbelianSheaf M)).homology n ≃ₗ[Γ(X, ⊤)] ModuleH M n :=
  (linearHomologyEquiv M U n).symm.trans (affineCoverCechEquiv M U hU hCover n)

/-- The same actual comparison after restricting scalars to the original base ring. -/
def affineRingCohomologyEquiv {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤)) (n : ℕ) :
    let _ := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n) ρ
    (complex U (moduleAbelianSheaf M)).homology n ≃ₗ[R] ModuleRingH ρ M n := by
  let _ := Module.compHom ((complex U (moduleAbelianSheaf M)).homology n) ρ
  exact
    { toAddEquiv := (affineCohomologyEquiv M U hU hCover n).toAddEquiv
      map_smul' := fun r x ↦ (affineCohomologyEquiv M U hU hCover n).map_smul (ρ r) x }

end FLT.Mazur.IncreasingCechScalars
