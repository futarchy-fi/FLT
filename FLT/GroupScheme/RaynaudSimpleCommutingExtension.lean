/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCommutativeImageScalars
public import FLT.GroupScheme.RaynaudRankOneScalarExtension

/-!
# Extension from a model with simple commuting generic action

Construct the scalar field from the actual simple representation and then
apply rank-one rigidity. No scalar field or integral scalar lifts are inputs.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K]
  (X : FF R K) (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
  [Module (ZMod p) X.Points]
  (ρ : Representation (ZMod p) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points)
  [ρ.IsIrreducible]

/-- Simple commuting generic action suffices for every prescribed extension. -/
theorem extend_from_simple_commuting_model
    (hact : ∀ σ x, ρ σ x = σ • x) (hcomm : ∀ σ τ, Commute (ρ σ) (ρ τ))
    (he : RaynaudParameters.order (p : R) < p - 1)
    (Y : FF R K) (g : GenericGaloisHom X Y) : ∃! h : ModelHom X Y, genericHom h = g := by
  obtain ⟨F, hF, hfin, hp, hmod, hdim, hs⟩ :=
    ρ.exists_rank_one_scalar_field_of_commuting hcomm p
  let : SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points :=
    ⟨fun a σ x ↦ by simpa only [hact] using (hs a σ x).symm⟩
  exact extend_from_rank_one_scalar_model (F := F) X p hdim he Y g

end ThreeAdicPlan
