/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIdentifiedCharacters
public import FLT.GroupScheme.RaynaudExtremalActions

/-!
# Derived character bases on the independently constructed extrema

The maximum and minimum, their generic identifications and their scalar
maps come from C5m7. Character bases are consequences of those constructions
and the generic point rank, rather than additional model data.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F]
  (X : FF R K) [Module F X.Points]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points]

/-- The independent maximum has rank-one character bases for its actual augmentation ideal. -/
theorem exists_maximal_model_character_bases (p : ℕ) [CharP F p]
    [CharP (ResidueField R) p] (hdim : Module.finrank F X.Points = 1) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M) (lift : F → ModelHom M M)
      (h1 : lift 1 = BialgHom.id R M.CoordinateRing)
      (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a)),
      Function.Bijective f ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom M Y), ∃! h : ModelHom M Y, genericHom h = g) ∧
      (∀ a x, genericHom (lift a) (f x) = f (a • x)) ∧
      (∀ χ : Fˣ →* Rˣ, Nonempty (Module.Basis Unit R (M.integralCharacter lift h1 hmul χ))) := by
  obtain ⟨M, f, lift, hf, hM, hlift, _, h1, _, hmul⟩ :=
    exists_maximal_model_scalar_action (F := F) X
  exact ⟨M, f, lift, h1, hmul, hf, hM, hlift,
    fun χ ↦ f.integralCharacter_basis hf p hdim lift h1 hmul hlift χ⟩

/-- The independent minimum has rank-one character bases for its actual augmentation ideal. -/
theorem exists_minimal_model_character_bases (p : ℕ) [CharP F p]
    [CharP (ResidueField R) p] (hdim : Module.finrank F X.Points = 1) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M) (lift : F → ModelHom M M)
      (h1 : lift 1 = BialgHom.id R M.CoordinateRing)
      (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a)),
      Function.Bijective f ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom Y M), ∃! h : ModelHom Y M, genericHom h = g) ∧
      (∀ a x, genericHom (lift a) (f x) = f (a • x)) ∧
      (∀ χ : Fˣ →* Rˣ, Nonempty (Module.Basis Unit R (M.integralCharacter lift h1 hmul χ))) := by
  obtain ⟨M, f, lift, hf, hM, hlift, _, h1, _, hmul⟩ :=
    exists_minimal_model_scalar_action (F := F) X
  exact ⟨M, f, lift, h1, hmul, hf, hM, hlift,
    fun χ ↦ f.integralCharacter_basis hf p hdim lift h1 hmul hlift χ⟩

end ThreeAdicPlan
