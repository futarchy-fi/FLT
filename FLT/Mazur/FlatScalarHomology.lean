/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Homology under flat extension of scalars

Flat scalar extension preserves the actual homology object of a module short
complex. In particular, a field extension preserves its homology dimension.
-/

@[expose] public noncomputable section
open CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FlatScalarHomology
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Actual scalar extension commutes with the actual short-complex homology object. -/
def homologyIso (φ : R →+* S) (hφ : φ.Flat) (C : ShortComplex (ModuleCat.{u} R)) :
    (ModuleCat.extendScalars φ).obj C.homology ≅
      (C.map (ModuleCat.extendScalars φ)).homology := by
  let _ := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact (C.mapHomologyIso (ModuleCat.extendScalars φ)).symm

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Over a field no extra flatness hypothesis is needed. -/
def fieldHomologyIso (C : ShortComplex (ModuleCat.{u} k)) :
    (ModuleCat.extendScalars (algebraMap k K)).obj C.homology ≅
      (C.map (ModuleCat.extendScalars (algebraMap k K))).homology :=
  homologyIso (algebraMap k K) (RingHom.flat_algebraMap_iff.mpr inferInstance) C

/-- A field extension preserves the dimension of actual module-complex homology. -/
theorem field_homology_finrank (C : ShortComplex (ModuleCat.{u} k)) :
    Module.finrank K (C.map (ModuleCat.extendScalars (algebraMap k K))).homology =
      Module.finrank k C.homology := by
  apply (fieldHomologyIso (k := k) (K := K) C).toLinearEquiv.finrank_eq.symm.trans
  let _ : Algebra k K := (algebraMap k K).toAlgebra
  exact Module.finrank_baseChange (R := K) (S := k) (M' := C.homology)

end FLT.Mazur.FlatScalarHomology
