/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePicardSections
public import FLT.Mazur.OpenModuleSectionScalars
public import FLT.Mazur.IncreasingCechFlatTerms
public import FLT.Mazur.IncreasingCechBaseComplex

/-!
# Flat Cech terms for line bundles in flat families

An affine line bundle has invertible, hence flat, sections over its affine
coordinate ring. Flatness of the structural morphism then gives flatness over
the base, also on all affine intersections of a finite cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FlatLineSectionTerms
open FCurve Chow IncreasingCechScalars IncreasingCechComplex

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S] [Flat f]
  (M : X.Modules) (hM : LocallyFreeRankOne M)

include hM in
/-- Over an affine source, a line's global sections are flat over the affine base. -/
theorem affineTop_flat [IsAffine X] :
    Module.Flat Γ(S, ⊤) (AffineCartesianSectionScalars.baseSections f M) := by
  let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let _ := SchemePicard.sections_invertible M hM
  let _ : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := f.flat_appTop
  let _ : Module Γ(S, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
  let _ : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans Γ(S, ⊤) Γ(X, ⊤) Γ(M, ⊤)

include hM in
/-- Affine-open sections of a line are flat with their original structural scalars. -/
theorem affineOpen_flat (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat Γ(S, ⊤) (baseSections M f.appTop.hom U) := by
  let _ : IsAffine U.toScheme := hU
  let _ := affineTop_flat (U.ι ≫ f) (M.restrict U.ι) (hM.restrict U.ι)
  exact Module.Flat.of_linearEquiv (OpenModuleSectionScalars.chartIso f M U).toLinearEquiv

/-- Increasing tuple coordinates, now for an arbitrary line coefficient. -/
def termEquiv {ι : Type} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    BaseTerm M U f.appTop.hom n ≃ₗ[Γ(S, ⊤)]
      (∀ a : Tuple (ι := ι) n, baseSections M f.appTop.hom (CechSheafHZero.V U n a.val)) :=
  { toFun := fun x ↦ x
    invFun := fun x ↦ x
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

include hM in
/-- Every actual bounded Cech term of a line on a separated flat family is base-flat. -/
theorem term_flat [X.IsSeparated] {ι : Type} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (a : Tuple (ι := ι) n) := affineOpen_flat f M hM (CechSheafHZero.V U n a.val)
    (affineCover_intersection_isAffineOpen U hU n a.val)
  let _ : Module.Flat Γ(S, ⊤)
      (∀ a : Tuple (ι := ι) n, baseSections M f.appTop.hom (CechSheafHZero.V U n a.val)) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype
      (R := Γ(S, ⊤))
      (M := fun a : Tuple (ι := ι) n ↦ baseSections M f.appTop.hom
        (CechSheafHZero.V U n a.val))).symm
  exact Module.Flat.of_linearEquiv (termEquiv f M U n)

end FLT.Mazur.FlatLineSectionTerms
