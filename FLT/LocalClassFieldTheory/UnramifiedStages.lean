/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedGaloisExistence
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Unramified stages in a chosen separably closed field

The stage predicate records an actual finite unramified Henselian DVR with
this fraction field. Normality and equal residue degree are consequences,
not fields of the predicate. Each positive degree is realized in the chosen
overfield by embedding the constructed Galois extension.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K E : Type u) [CommRing R] [Field K] [Field E]
  [Algebra R K] [Algebra K E] [Algebra R E]

/-- An actual finite unramified Henselian integral model of a fraction extension. -/
def IsUnramifiedStage : Prop :=
  FiniteDimensional K E ∧
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Module.Finite R S) (_ : FaithfulSMul R S)
      (_ : Algebra S E) (_ : IsFractionRing S E) (_ : IsScalarTower R S E),
      Algebra.FormallyUnramified R S ∧ HenselianLocalRing S

variable {R K E}
  [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
  [IsScalarTower R K E] [Finite (ResidueField R)]

omit [IsFractionRing R K] in
/-- Every stage is normal by its constructed splitting generator. -/
theorem IsUnramifiedStage.normal (h : IsUnramifiedStage R K E) : Normal K E := by
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, hu, hh⟩ := h
  let := hu
  let := hh
  exact normal_of_unramified (R := R) (S := S)

variable (C : Type u) [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [IsSepClosed C] [IsAdicComplete (maximalIdeal R) R]

/-- Every positive degree occurs as an actual unramified intermediate field
of the chosen separably closed overfield. -/
theorem exists_unramified_stage (n : ℕ) [NeZero n] :
    ∃ E : IntermediateField K C, IsUnramifiedStage R K E ∧ Module.finrank K E = n := by
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, _, hu, _, hh, hd⟩ :=
    exists_galois_unramified_degree (R := R) (K := K) n
  let f : L →ₐ[K] C := IsSepClosed.lift
  let E := f.fieldRange
  let e : L ≃ₐ[K] E := f.equivFieldRange
  let : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let algSE : Algebra S E := (e.toRingHom.comp (algebraMap S L)).toAlgebra
  let es : L ≃ₐ[S] E := { e.toRingEquiv with commutes' := fun _ => rfl }
  let : IsFractionRing S E := IsFractionRing.of_algEquiv es
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R E r = e (algebraMap S L (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply R K L, e.commutes,
      ← IsScalarTower.algebraMap_apply R K E]
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R L
    simpa only [← IsScalarTower.algebraMap_apply R S L] using congrArg (algebraMap S L) h)
  refine ⟨E, ⟨inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, algSE, inferInstance, inferInstance, hu, hh⟩, ?_⟩
  exact e.toLinearEquiv.finrank_eq.symm.trans hd

end LocalClassFieldTheory
