/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCohomology
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Explicit linear cycles and boundaries of the bounded Cech complex

The categorical cohomology of the increasing complex is the actual quotient
of its linear cycles by boundaries. Compatibility with coefficient
multiplication identifies the quotient action, including in degree zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex CechSortingMaps FCurve

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

/-- Expose the actual scalar action on the categorical bounded terms. -/
instance complexTermModule (n : ℕ) :
    Module Γ(X, ⊤) ((complex U (moduleAbelianSheaf M)).X n) := termModule M U n

/-- All categorical differentials commute with actual coefficient multiplication. -/
lemma complex_d_smul (i j : ℕ) (r : Γ(X, ⊤))
    (x : (complex U (moduleAbelianSheaf M)).X i) :
    (complex U (moduleAbelianSheaf M)).d i j (r • x) =
      r • (complex U (moduleAbelianSheaf M)).d i j x :=
  ConcreteCategory.congr_hom ((coefficientMap U (moduleMultiply M r)).comm i j) x

/-- The original categorical differential, with its actual linear structure. -/
def complexLinearDifferential (i j : ℕ) :
    (complex U (moduleAbelianSheaf M)).X i →ₗ[Γ(X, ⊤)]
      (complex U (moduleAbelianSheaf M)).X j where
  toFun := (complex U (moduleAbelianSheaf M)).d i j
  map_add' := map_add _
  map_smul' := complex_d_smul M U i j

/-- Actual cycles of the bounded complex. -/
def cycles (n : ℕ) : Submodule Γ(X, ⊤) ((complex U (moduleAbelianSheaf M)).X n) :=
  (complexLinearDifferential M U n ((ComplexShape.up ℕ).next n)).ker

/-- The incoming differential takes values in the actual cycles. -/
def toCycles (n : ℕ) :
    (complex U (moduleAbelianSheaf M)).X ((ComplexShape.up ℕ).prev n) →ₗ[Γ(X, ⊤)]
      cycles M U n where
  toFun x := ⟨(complex U (moduleAbelianSheaf M)).d _ n x,
    ((complex U (moduleAbelianSheaf M)).sc n).ab_zero_apply x⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (complex_d_smul M U _ n r x)

/-- Actual boundaries inside cycles, including the zero incoming map in degree zero. -/
def boundaries (n : ℕ) : Submodule Γ(X, ⊤) (cycles M U n) := (toCycles M U n).range

/-- The canonical quotient description of bounded categorical homology. -/
def homologyQuotientAddEquiv (n : ℕ) :
    (complex U (moduleAbelianSheaf M)).homology n ≃+ (cycles M U n ⧸ boundaries M U n) :=
  ((complex U (moduleAbelianSheaf M)).sc n).abHomologyIso.addCommGroupIsoToAddEquiv

/-- Actual coefficient multiplication on the explicit quotient homology data. -/
def scalarHomologyData (n : ℕ) (r : Γ(X, ⊤)) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map
        (coefficientMap U (moduleMultiply M r)))
      ((complex U (moduleAbelianSheaf M)).sc n).abLeftHomologyData
      ((complex U (moduleAbelianSheaf M)).sc n).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (cycles M U n) r)
  φH := AddCommGrpCat.ofHom
    (DistribSMul.toAddMonoidHom (cycles M U n ⧸ boundaries M U n) r)
  commi := by ext x; rfl
  commf' := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact (complex_d_smul M U _ n r x).symm
  commπ := by ext x; rfl

/-- The actual quotient and sorting actions coincide. -/
lemma homologyQuotientAddEquiv_smul (n : ℕ) (r : Γ(X, ⊤))
    (x : (complex U (moduleAbelianSheaf M)).homology n) :
    homologyQuotientAddEquiv M U n (r • x) = r • homologyQuotientAddEquiv M U n x := by
  rw [homology_smul]
  exact ConcreteCategory.congr_hom (scalarHomologyData M U n r).homologyMap_comm x

/-- The actual bounded cohomology is linearly the cycles/boundaries quotient. -/
def homologyQuotientEquiv (n : ℕ) :
    (complex U (moduleAbelianSheaf M)).homology n ≃ₗ[Γ(X, ⊤)]
      (cycles M U n ⧸ boundaries M U n) where
  toAddEquiv := homologyQuotientAddEquiv M U n
  map_smul' := homologyQuotientAddEquiv_smul M U n

end FLT.Mazur.IncreasingCechScalars
