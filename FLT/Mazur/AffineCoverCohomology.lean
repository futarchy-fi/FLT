/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoverIntersections
public import FLT.Mazur.ModuleCechScalar
public import FLT.Mazur.ModuleOpenCohomology

/-!
# Cohomology from an affine open cover

On a separated scheme, the Cech complex of any affine open cover computes
quasi-coherent module cohomology. The comparison is natural in the module and
linear over global sections, and remains linear after restriction along any
base-ring homomorphism. No finiteness assumption on the cover is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero CechAcyclicCokernel CechAcyclicNaturality

local instance affineCoverHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
  (M : X.Modules) [M.IsQuasicoherent] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

include hU in
/-- Vanishing on the open subschemes gives ambient acyclicity on every tuple. -/
theorem affineCoverAcyclic : CoverAcyclic U (moduleAbelianSheaf M) := by
  intro n q a
  have h := affineCover_intersection_moduleH_succ_subsingleton M U hU n q a
  exact ⟨fun x y ↦ (moduleOpenHEquiv (V U n a) M (q + 1)).injective (h.elim _ _)⟩

variable (hCover : iSup U = ⊤)

/-- An affine open cover computes module cohomology over the global section ring. -/
def affineCoverCechEquiv (n : ℕ) :
    CH U (moduleAbelianSheaf M) n ≃ₗ[Γ(X, ⊤)] ModuleH M n :=
  moduleCechEquiv M U hCover (affineCoverAcyclic M U hU) n

/-- The affine-cover computation commutes with coefficient morphisms. -/
lemma affineCoverCechEquiv_naturality {N : X.Modules} [N.IsQuasicoherent]
    (g : M ⟶ N) (n : ℕ) (x : CH U (moduleAbelianSheaf M) n) :
    affineCoverCechEquiv N U hU hCover n
        (CHmap U ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n x) =
      moduleHMap g n (affineCoverCechEquiv M U hU hCover n x) :=
  acyclicCoverEquiv_naturality U hCover
    (affineCoverAcyclic M U hU) (affineCoverAcyclic N U hU)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n x

/-- The same computation is linear over any ring acting through global sections. -/
def affineCoverRingCechEquiv {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤)) (n : ℕ) :
    letI _cechRModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
    letI _cohomologyRModule := Module.compHom (ModuleH M n) ρ
    CH U (moduleAbelianSheaf M) n ≃ₗ[R] ModuleH M n := by
  letI _cechRModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
  letI _cohomologyRModule := Module.compHom (ModuleH M n) ρ
  exact
    { toAddEquiv := (affineCoverCechEquiv M U hU hCover n).toAddEquiv
      map_smul' := fun r x ↦ (affineCoverCechEquiv M U hU hCover n).map_smul (ρ r) x }

/-- Restricting scalars preserves naturality of the affine-cover computation. -/
lemma affineCoverRingCechEquiv_naturality {R : Type v} [Ring R]
    (ρ : R →+* Γ(X, ⊤)) {N : X.Modules} [N.IsQuasicoherent] (g : M ⟶ N)
    (n : ℕ) (x : CH U (moduleAbelianSheaf M) n) :
    affineCoverRingCechEquiv N U hU hCover ρ n
        (CHmap U ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n x) =
      moduleHMap g n (affineCoverRingCechEquiv M U hU hCover ρ n x) :=
  affineCoverCechEquiv_naturality M U hU hCover g n x

/-- The structure morphism gives the existing field-valued cohomology specialization. -/
def affineCoverScalarCechEquiv {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    letI _cechFieldModule :=
      Module.compHom (CH U (moduleAbelianSheaf M) n) (structureScalarMap f)
    CH U (moduleAbelianSheaf M) n ≃ₗ[k] ModuleScalarH f M n :=
  moduleScalarCechEquiv M U hCover (affineCoverAcyclic M U hU) f n

end FLT.Mazur.FCurve
