/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Generators lifted from relative cotangent spaces

For a finitely generated ideal in the Jacobson radical, generators of its
cotangent module lift to generators of the ideal. Over a local base, it
suffices to lift a basis of the residual cotangent module.
-/

@[expose] public noncomputable section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- Nakayama lifts generators of the cotangent module of a radical ideal to
generators of the ideal itself. -/
theorem span_eq_of_span_toCotangent_eq_top (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ jacobson (⊥ : Ideal A)) {ι : Type*} (x : ι → I)
    (hx : Submodule.span A (Set.range (fun i ↦ I.toCotangent (x i))) = ⊤) :
    Ideal.span (Set.range (fun i ↦ (x i : A))) = I := by
  let : Module.Finite A I := Module.Finite.of_fg hI
  let N := Submodule.span A (Set.range x)
  have hN : N.map I.toCotangent = ⊤ := by
    simpa only [N, Submodule.map_span, ← Set.range_comp, Function.comp_def] using hx
  have htop : N = ⊤ := by
    apply top_unique
    have hmap := congrArg (Submodule.comap I.toCotangent) hN
    rw [Submodule.comap_map_eq, Submodule.comap_top] at hmap
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.Finite.fg_top (R := A) (M := I)) hjac
    · rw [show I.toCotangent.ker = I • ⊤ from Submodule.ker_mkQ _] at hmap
      exact hmap.ge
  have h := congrArg (Submodule.map I.subtype) htop
  simpa only [N, Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply] using h

end Ideal

namespace Ideal

open scoped TensorProduct

variable {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]

/-- Lifts of a basis of the residual cotangent module generate the original
ideal, by Nakayama over the base and then over the algebra. -/
theorem span_eq_of_residual_cotangent_basis (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ jacobson (⊥ : Ideal A)) [Module.Finite R I.Cotangent]
    {ι : Type*} (x : ι → I)
    (b : Module.Basis ι (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] I.Cotangent))
    (hb : ∀ i, 1 ⊗ₜ[R] I.toCotangent (x i) = b i) :
    Ideal.span (Set.range (fun i ↦ (x i : A))) = I := by
  apply I.span_eq_of_span_toCotangent_eq_top hI hjac x
  apply Submodule.span_eq_top_of_span_eq_top R A
  exact IsLocalRing.span_eq_top_of_tmul_eq_basis _ b hb

/-- A radical ideal admits generators indexed by the dimension of its
residual cotangent module; the generators lift a basis of that module. -/
theorem exists_generators_of_residual_cotangent (I : Ideal A) (hI : I.FG)
    (hjac : I ≤ jacobson (⊥ : Ideal A)) [Module.Finite R I.Cotangent] :
    ∃ x : Fin (Module.finrank (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] I.Cotangent)) → I,
      Ideal.span (Set.range (fun i ↦ (x i : A))) = I ∧
      ∀ i, 1 ⊗ₜ[R] I.toCotangent (x i) =
        Module.finBasis (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] I.Cotangent) i := by
  have hsurj : Function.Surjective (fun x : I ↦
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] I.toCotangent x) :=
    (TensorProduct.mk_surjective R I.Cotangent (IsLocalRing.ResidueField R)
      Ideal.Quotient.mk_surjective).comp I.toCotangent_surjective
  choose x hx using fun i ↦ hsurj (Module.finBasis (IsLocalRing.ResidueField R)
    ((IsLocalRing.ResidueField R) ⊗[R] I.Cotangent) i)
  exact ⟨x, I.span_eq_of_residual_cotangent_basis hI hjac x _ hx, hx⟩

end Ideal

namespace AlgHom

open scoped TensorProduct

variable {R A : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing A] [IsLocalRing A] [Algebra R A] [Module.Finite R A]

/-- The augmentation ideal of a finite local algebra has generators lifting
a basis of its residual invariant cotangent module. The number of generators
is the dimension of that module, rather than the rank of the whole algebra. -/
theorem exists_augmentation_generators (ε : A →ₐ[R] R) :
    ∃ x : Fin (Module.finrank (IsLocalRing.ResidueField R)
        ((IsLocalRing.ResidueField R) ⊗[R] (RingHom.ker ε).Cotangent)) → RingHom.ker ε,
      Ideal.span (Set.range (fun i ↦ (x i : A))) = RingHom.ker ε ∧
      ∃ b : Module.Basis _ (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] (RingHom.ker ε).Cotangent),
        ∀ i, 1 ⊗ₜ[R] (RingHom.ker ε).toCotangent (x i) = b i := by
  let I := RingHom.ker ε
  let : Module.Finite R I.Cotangent := Module.Finite.of_surjective
    (I.toCotangent.restrictScalars R) I.toCotangent_surjective
  have hjac : I ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
  obtain ⟨x, hx, hb⟩ := I.exists_generators_of_residual_cotangent (R := R)
    ((IsNoetherian.noetherian (I.restrictScalars R)).of_restrictScalars R) hjac
  exact ⟨x, hx, _, hb⟩

end AlgHom
