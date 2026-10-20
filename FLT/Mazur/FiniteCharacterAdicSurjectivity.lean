/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicJacobson
public import FLT.Mazur.DiagonalizableCoefficientReduction
public import Mathlib.RingTheory.Nakayama

/-!
# Lifting finite-character coordinate surjectivity from the initial reduction

The entire character coefficient kernel consists of defining-ideal multiples.
Finite generation over the original complete base lets Nakayama lift
surjectivity of an actual coordinate algebra map from its initial reduction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteCharacterAdicElements

open DiagonalizableCobar

variable {R G : Type} [CommRing R] [AddCommMonoid G] (I : Ideal R)

/-- Every element of the full character kernel is an original defining-ideal multiple. -/
theorem coefficientIdeal_le_smul_top {p : AddMonoidAlgebra R G}
    (hp : p ∈ coefficientIdeal R G I) :
    p ∈ I • (⊤ : Submodule R (AddMonoidAlgebra R G)) := by
  have hc := (mem_coefficientIdeal R G I p).mp hp
  rw [← p.sum_coeff_single]
  apply Submodule.sum_mem
  intro a _
  have he : AddMonoidAlgebra.single a (p.coeff a) =
      (p.coeff a) • AddMonoidAlgebra.single a (1 : R) := by simp
  rw [he]
  exact Submodule.smul_mem_smul (hc a) Submodule.mem_top

variable [Finite G] [IsAdicComplete I R]
  {C : Type} [CommRing C] [Algebra R C]

/-- Surjectivity of the whole initial coordinate reduction lifts over the original complete base. -/
theorem surjective_of_initial_reduction (f : C →ₐ[R] AddMonoidAlgebra R G)
    (hf : Function.Surjective ((coefficientReduction R G I).comp f)) :
    Function.Surjective f := by
  let _ : Module.Finite R (AddMonoidAlgebra R G) :=
    Module.Finite.of_basis (AddMonoidAlgebra.basis G R)
  apply LinearMap.surjective_of_surjective_comp_mkQ f.toLinearMap I
    (IsAdicComplete.le_jacobson_bot I)
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨c, hc⟩ := hf (coefficientReduction R G I x)
    refine ⟨c, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    apply coefficientIdeal_le_smul_top I
    change coefficientReduction R G I (f c - x) = 0
    change coefficientReduction R G I (f c) = coefficientReduction R G I x at hc
    rw [map_sub, hc, sub_self]

end FLT.Mazur.FiniteCharacterAdicElements
