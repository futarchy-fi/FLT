/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteImageField
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Hermite finiteness for continuous representations with bounded discriminant

There are finitely many representations into a fixed finite discrete group
whose kernel fields have bounded discriminant. Ramification restrictions do
not enter this theorem: deriving such a bound from them is a separate input.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions

local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "E" => AlgebraicClosure ℚ

/-- A finite Galois subfield of the rational algebraic closure is a number field. -/
instance finiteGaloisIntermediateField_numberField (L : FiniteGaloisIntermediateField ℚ E) :
    NumberField L where

/-- Hermite finiteness restricted to finite Galois subfields of the chosen closure. -/
theorem finite_galoisFields_discr_bdd (B : ℕ) :
    {L : FiniteGaloisIntermediateField ℚ E | |NumberField.discr L| ≤ B}.Finite := by
  let j : FiniteGaloisIntermediateField ℚ E →
      {L : IntermediateField ℚ E // FiniteDimensional ℚ L} :=
    fun L ↦ ⟨L.toIntermediateField, inferInstance⟩
  have hj : Function.Injective j := fun _ _ h ↦
    FiniteGaloisIntermediateField.val_injective (congrArg Subtype.val h)
  exact (NumberField.finite_of_discr_bdd E B).preimage (f := j) hj.injOn

variable {H : Type*} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]

omit [Group H] [TopologicalSpace H] [DiscreteTopology H] in
/-- Finitely many coefficient functions can inflate from a given finite Galois field. -/
theorem finite_inflatedFunctions (L : FiniteGaloisIntermediateField ℚ E) :
    (Set.range fun a : Gal(L/ℚ) → H ↦
      fun g : G ↦ a (AlgEquiv.restrictNormalHom L g)).Finite := Set.finite_range _

/-- A discriminant bound gives finiteness of actual continuous homomorphisms,
including all choices of frame and nonsurjective homomorphisms. -/
theorem finite_representations_discr_bdd (B : ℕ) :
    {f : G →ₜ* H | |NumberField.discr (finiteImageField f)| ≤ B}.Finite := by
  let S := {L : FiniteGaloisIntermediateField ℚ E | |NumberField.discr L| ≤ B}
  have hS : S.Finite := finite_galoisFields_discr_bdd B
  have hU := hS.biUnion (fun L _ ↦ finite_inflatedFunctions (H := H) L)
  have hi : Function.Injective (fun f : G →ₜ* H ↦ (f : G → H)) := by
    intro f g h
    ext x
    exact congrFun h x
  apply (hU.preimage hi.injOn).subset
  intro f hf
  simp only [Set.mem_preimage, Set.mem_iUnion]
  exact ⟨finiteImageField f, hf, finiteImageRepresentation f,
    funext (finiteImageRepresentation_restrict f)⟩

/-- A family of finite representations is finite once its kernel discriminants
are uniformly bounded. This does not assume finiteness of the family itself. -/
theorem finite_representations_of_discr_bound (S : Set (G →ₜ* H))
    (B : ℕ) (hB : ∀ f ∈ S, |NumberField.discr (finiteImageField f)| ≤ B) : S.Finite :=
  (finite_representations_discr_bdd B).subset hB

end GaloisRepresentation.Extensions
