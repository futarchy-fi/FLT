/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedLocalConstantFiberRank
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Flatness from constant field-fiber dimension over a reduced ring

The local basis construction applies at every maximal ideal. Flatness then
descends from these actual module localizations to the original finite module.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open TensorProduct

namespace FLT.Mazur.ReducedConstantFiberFlat

universe u
variable {R M : Type u} [CommRing R] [IsReduced R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module with constant dimension on all field tests over a reduced base is flat. -/
theorem flat_of_constant_field_dimension (n : ℕ)
    (hd : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = n) : Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro p _
  let S := Localization.AtPrime p
  have hfree : Module.Free S (S ⊗[R] M) := by
    apply ReducedLocalConstantFiberRank.free_of_constant_field_dimension n
    intro K _ _
    let _ : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
    let _ : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rw [(AlgebraTensorModule.cancelBaseChange R S K K M).finrank_eq]
    exact hd K
  let _ := hfree
  let _ : Module.Free S (LocalizedModule p.primeCompl M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct p.primeCompl M).symm
  exact Module.Flat.trans R S _

end FLT.Mazur.ReducedConstantFiberFlat
