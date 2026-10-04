/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.LocalRing.ResidueGenerators
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Generator bounds descend along local base change -/

@[expose] public noncomputable section

open TensorProduct

namespace IsLocalRing

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The residue dimensions agree under a specified local base change. -/
theorem residue_finrank_eq_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) =
      Module.finrank (ResidueField S) (ResidueField S ⊗[S] N) := by
  let e := (AlgebraTensorModule.cancelBaseChange R (ResidueField R)
    (ResidueField S) (ResidueField S) M).trans
      ((AlgebraTensorModule.cancelBaseChange R S (ResidueField S) (ResidueField S) M).symm.trans
        (hf.equiv.baseChange S (ResidueField S) _ _))
  simpa only [Module.finrank_baseChange] using e.finrank_eq

/-- A specified finite generating family bounds the dimension of the residue module. -/
theorem residue_finrank_le_of_generators {n : ℕ} (v : Fin n → N)
    (hv : Submodule.span S (Set.range v) = ⊤) :
    Module.finrank (ResidueField S) (ResidueField S ⊗[S] N) ≤ n := by
  let g := Finsupp.linearCombination S v
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  have hs := g.lTensor_surjective (ResidueField S) hg
  have h := LinearMap.finrank_le_finrank_of_surjective (f := g.baseChange (ResidueField S)) hs
  simpa only [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin] using h

/-- Generator cardinality descends to the original finite module over a local ring.
No choice of descending geometric generators is assumed. -/
theorem exists_generators_of_isBaseChange [Module.Finite R M]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) {n : ℕ} (v : Fin n → N)
    (hv : Submodule.span S (Set.range v) = ⊤) :
    ∃ d ≤ n, ∃ w : Fin d → M, Submodule.span R (Set.range w) = ⊤ := by
  apply exists_generators_of_residue_finrank_le R M
  rw [residue_finrank_eq_of_isBaseChange hf]
  exact residue_finrank_le_of_generators v hv

end IsLocalRing
