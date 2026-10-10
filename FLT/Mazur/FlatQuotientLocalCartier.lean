/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatQuotientCartierFiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Local Cartier detection from the actual residue fiber

A regular principal fiber ideal supplies its own lifted equation. With finite
presentation of the original ideal, flatness lifts that equation and its
regularity. Over a Noetherian ambient the finite presentation is automatic.
-/

@[expose] public noncomputable section
open TensorProduct IsLocalRing
namespace FLT.Mazur.FCurve

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The fiber projection for a quotient of the coefficient ring is surjective. -/
theorem coefficient_quotient_projection_surjective (J : Ideal R) :
    Function.Surjective (Algebra.TensorProduct.includeRight
      (R := R) (A := R ⧸ J) (B := B)) :=
  TensorProduct.mk_surjective R B (R ⧸ J) Ideal.Quotient.mk_surjective

/-- The fiber equation can be chosen and lifted from the actual extended ideal. -/
theorem exists_regular_generator_of_flat_quotient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (I : Ideal B) [Module.Flat R B] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I]
    (hf : ∃ b : (R ⧸ J) ⊗[R] B, IsRegular b ∧
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := R ⧸ J)) =
        Ideal.span {b}) : ∃ a : B, IsRegular a ∧ I = Ideal.span {a} := by
  obtain ⟨b, hb, hIb⟩ := hf
  have hm : b ∈ I.map (Algebra.TensorProduct.includeRight (R := R) (A := R ⧸ J)) :=
    hIb ▸ Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨a, ha, hab⟩ := (Ideal.mem_map_iff_of_surjective _
    (coefficient_quotient_projection_surjective (B := B) J)).mp hm
  have he : (1 ⊗ₜ[R] a : (R ⧸ J) ⊗[R] B) = b := hab
  exact ⟨a, regular_generator_of_flat_quotient_fiber J hJ I a ha
    (he ▸ hb) (hIb.trans (congrArg (fun x ↦ Ideal.span {x}) he.symm))⟩

/-- Local maps put the extended maximal ideal in the required Jacobson radical. -/
theorem exists_regular_generator_of_local_fiber [IsLocalRing R] [IsLocalRing B]
    [IsLocalHom (algebraMap R B)] (I : Ideal B)
    [Module.Flat R B] [Module.Flat R (B ⧸ I)] [Module.FinitePresentation B I]
    (hf : ∃ b : ResidueField R ⊗[R] B, IsRegular b ∧
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R)) =
        Ideal.span {b}) : ∃ a : B, IsRegular a ∧ I = Ideal.span {a} := by
  apply exists_regular_generator_of_flat_quotient_fiber (maximalIdeal R) _ I hf
  rw [jacobson_eq_maximalIdeal _ bot_ne_top]
  exact ((local_hom_TFAE (algebraMap R B)).out 1 3 rfl rfl).mp inferInstance

/-- Noetherian local ambients need no additional finite-presentation hypothesis. -/
theorem exists_regular_generator_of_noetherian_local_fiber
    [IsLocalRing R] [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom (algebraMap R B)] (I : Ideal B)
    [Module.Flat R B] [Module.Flat R (B ⧸ I)]
    (hf : ∃ b : ResidueField R ⊗[R] B, IsRegular b ∧
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R)) =
        Ideal.span {b}) : ∃ a : B, IsRegular a ∧ I = Ideal.span {a} := by
  let _ : Module.FinitePresentation B I := Module.finitePresentation_of_finite B I
  exact exists_regular_generator_of_local_fiber I hf

end FLT.Mazur.FCurve
