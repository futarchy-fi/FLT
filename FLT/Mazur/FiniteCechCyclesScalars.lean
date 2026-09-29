/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCechTermScalars
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Cech homology as a module quotient

The actual linear differentials define cycles and boundaries. Their quotient
identifies with categorical Cech homology, with its existing coefficient scalar
action. The construction includes degree zero and restriction to any base ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X : Scheme.{u}} {ι : Type u} (M : X.Modules) (U : ι → X.Opens)

/-- Cycles are the kernel of the actual outgoing differential. -/
def finiteCechCycles (n : ℕ) : Submodule Γ(X, ⊤) ((C U (moduleAbelianSheaf M)).X n) :=
  (finiteCechDifferential M U n ((ComplexShape.up ℕ).next n)).ker

/-- The incoming differential takes values in cycles, also in degree zero. -/
def finiteCechToCycles (n : ℕ) :
    (C U (moduleAbelianSheaf M)).X ((ComplexShape.up ℕ).prev n) →ₗ[Γ(X, ⊤)]
      finiteCechCycles M U n where
  toFun x := ⟨(C U (moduleAbelianSheaf M)).d _ n x,
    ((C U (moduleAbelianSheaf M)).sc n).ab_zero_apply x⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (finiteCech_d_smul M U _ n r x)

/-- Boundaries form the image submodule inside cycles. -/
def finiteCechBoundaries (n : ℕ) : Submodule Γ(X, ⊤) (finiteCechCycles M U n) :=
  (finiteCechToCycles M U n).range

/-- The quotient description of categorical homology on underlying additive groups. -/
def finiteCechHomologyAddEquiv (n : ℕ) :
    CH U (moduleAbelianSheaf M) n ≃+
      (finiteCechCycles M U n ⧸ finiteCechBoundaries M U n) :=
  ((C U (moduleAbelianSheaf M)).sc n).abHomologyIso.addCommGroupIsoToAddEquiv

/-- The coefficient action on explicit cycles and on their quotient. -/
def finiteCechScalarHomologyData (n : ℕ) (r : Γ(X, ⊤)) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map
        ((cechComplexFunctor U).map (moduleMultiply M r).hom))
      ((C U (moduleAbelianSheaf M)).sc n).abLeftHomologyData
      ((C U (moduleAbelianSheaf M)).sc n).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (finiteCechCycles M U n) r)
  φH := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom
    (finiteCechCycles M U n ⧸ finiteCechBoundaries M U n) r)
  commi := by
    ext x
    rfl
  commf' := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact (finiteCech_d_smul M U _ n r x).symm
  commπ := by
    ext x
    rfl

/-- The explicit quotient action is the existing coefficient action on CH. -/
lemma finiteCechHomologyAddEquiv_smul (n : ℕ) (r : Γ(X, ⊤))
    (x : CH U (moduleAbelianSheaf M) n) :
    finiteCechHomologyAddEquiv M U n (r • x) =
      r • finiteCechHomologyAddEquiv M U n x :=
  ConcreteCategory.congr_hom (finiteCechScalarHomologyData M U n r).homologyMap_comm x

/-- Categorical Cech homology is linearly the cycles/boundaries quotient. -/
def finiteCechHomologyEquiv (n : ℕ) :
    CH U (moduleAbelianSheaf M) n ≃ₗ[Γ(X, ⊤)]
      (finiteCechCycles M U n ⧸ finiteCechBoundaries M U n) where
  toAddEquiv := finiteCechHomologyAddEquiv M U n
  map_smul' := finiteCechHomologyAddEquiv_smul M U n

variable {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤))

/-- Cycles as a submodule over the chosen base ring. -/
def finiteCechRingCycles (n : ℕ) :
    letI _termModule := fun i ↦ Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
    Submodule R ((C U (moduleAbelianSheaf M)).X n) := by
  letI _termModule := fun i ↦ Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
  exact (finiteCechRingDifferential M U ρ n ((ComplexShape.up ℕ).next n)).ker

/-- The base-ring linear incoming differential, valued in cycles. -/
def finiteCechRingToCycles (n : ℕ) :
    letI _termModule := fun i ↦ Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
    (C U (moduleAbelianSheaf M)).X ((ComplexShape.up ℕ).prev n) →ₗ[R]
      finiteCechRingCycles M U ρ n := by
  letI _termModule := fun i ↦ Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
  exact
    { toFun := fun x ↦ ⟨(C U (moduleAbelianSheaf M)).d _ n x,
        ((C U (moduleAbelianSheaf M)).sc n).ab_zero_apply x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
      map_smul' := fun r x ↦ Subtype.ext (finiteCech_d_smul M U _ n (ρ r) x) }

/-- Boundaries as an actual base-ring submodule of cycles. -/
def finiteCechRingBoundaries (n : ℕ) :
    Submodule R (finiteCechRingCycles M U ρ n) := by
  letI _termModule := fun i ↦ Module.compHom ((C U (moduleAbelianSheaf M)).X i) ρ
  exact (finiteCechRingToCycles M U ρ n).range

/-- The quotient computation remains linear over an arbitrary base ring. -/
def finiteCechRingHomologyEquiv (n : ℕ) :
    letI _cohomologyModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
    CH U (moduleAbelianSheaf M) n ≃ₗ[R]
      (finiteCechRingCycles M U ρ n ⧸ finiteCechRingBoundaries M U ρ n) := by
  letI _cohomologyModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
  exact
    { toAddEquiv := finiteCechHomologyAddEquiv M U n
      map_smul' := fun r x ↦ finiteCechHomologyAddEquiv_smul M U n (ρ r) x }

end FLT.Mazur.FCurve
