/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAgreedPointAction
public import FLT.GroupScheme.RaynaudRepresentationContinuity
public import FLT.GroupScheme.RaynaudInertiaSimpleScalars

/-!
# Actual model subquotients compatible with local inertia

Choose a maximal proper inertia subrepresentation. Its smaller kernel and
simple quotient have actual finite-flat models. The quotient scalar field
is constructed by the wild/tame theorem and commutes with the model action.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {R K L : Type} [CommRing R] [Field K] [Field L] [NumberField L]
  [Algebra R K] [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers L)) p]
  (X : FF R K) [Module (ZMod p) X.Points] [Nontrivial X.Points]
  (ρ : Representation (ZMod p) (localInertiaGroup v) X.Points)
  (hρ : ρ.IsDiscreteContinuous)
  (ha : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∃ t : localInertiaGroup v,
    ∀ x : X.Points, σ • x = ρ t x)

include hρ ha in
/-- A compatible nonzero point module has a smaller compatible kernel and a scalar-line quotient. -/
theorem exists_compatible_scalar_quotient :
    ∃ (S Q : FF R K) (i : GenericGaloisHom S X) (q : GenericGaloisHom X Q),
      Function.Injective i ∧ Function.Surjective q ∧
      (∀ x, q x = 0 ↔ ∃ s, i s = x) ∧
      ∃ (_ : Module (ZMod p) S.Points)
        (ρS : Representation (ZMod p) (localInertiaGroup v) S.Points),
        ρS.IsDiscreteContinuous ∧
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∃ t : localInertiaGroup v,
          ∀ s : S.Points, σ • s = ρS t s) ∧
        Nat.card S.Points < Nat.card X.Points ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F Q.Points)
          (_ : SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q.Points),
          Module.finrank F Q.Points = 1 := by
  obtain ⟨W, hW⟩ := ρ.exists_coatom_subrepresentation
  let WG := X.agreedSubrepresentation p ρ ha W
  let ρQ := ρ.quotient W.toSubmodule W.apply_mem_toSubmodule
  let ρGQ := (X.primeRepresentation p).quotient W.toSubmodule WG.apply_mem_toSubmodule
  let ρGS : Representation (ZMod p) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      W.toSubmodule := (X.primeRepresentation p).subrepresentation W.toSubmodule
        WG.apply_mem_toSubmodule
  let : DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W.toSubmodule :=
    DistribMulAction.compHom _ ρGS
  let : DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (X.Points ⧸ W.toSubmodule) := DistribMulAction.compHom _ ρGQ
  let i : W.toSubmodule →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] X.Points :=
    { toAddMonoidHom := W.toSubmodule.subtype.toAddMonoidHom
      map_smul' := fun _ _ ↦ rfl }
  let q : X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K]
      (X.Points ⧸ W.toSubmodule) :=
    { toAddMonoidHom := W.toSubmodule.mkQ.toAddMonoidHom
      map_smul' := fun _ _ ↦ rfl }
  let S := FF.ofIsFiniteFlat W.toSubmodule
    (X.isFiniteFlat.subobject R K (AlgebraicClosure K) X.Points i Subtype.val_injective)
  let Q := FF.ofIsFiniteFlat (X.Points ⧸ W.toSubmodule)
    (X.isFiniteFlat.quotient R K (AlgebraicClosure K) X.Points q W.toSubmodule.mkQ_surjective)
  let : Finite (X.Points ⧸ W.toSubmodule) :=
    Finite.of_surjective W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
  let : ρQ.IsIrreducible := ρ.quotient_irreducible_of_isCoatom W hW
  let : TopologicalSpace (Module.End (ZMod p) (X.Points ⧸ W.toSubmodule))ˣ := ⊥
  let : DiscreteTopology (Module.End (ZMod p) (X.Points ⧸ W.toSubmodule))ˣ := ⟨rfl⟩
  obtain ⟨F, hF, hfin, hp, hm, hdim, hs⟩ :=
    LocalRamification.exists_rank_one_scalar_field_of_local_inertia v p ρQ
      ((ρQ.continuous_toHomUnits_iff_discrete).mpr (hρ.quotient ρ W))
  have hqAgree (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      ∃ t : localInertiaGroup v, ∀ y : X.Points ⧸ W.toSubmodule, σ • y = ρQ t y := by
    obtain ⟨t, ht⟩ := ha σ
    refine ⟨t, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := W.toSubmodule.mkQ_surjective y
    exact congrArg W.toSubmodule.mkQ (ht x)
  have hcomm : SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (X.Points ⧸ W.toSubmodule) := by
    constructor
    intro a σ y
    obtain ⟨t, ht⟩ := hqAgree σ
    rw [ht, ht]
    exact (hs a t y).symm
  refine ⟨S, Q, i, q, Subtype.val_injective, W.toSubmodule.mkQ_surjective, ?_,
    inferInstanceAs (Module (ZMod p) W.toSubmodule), W.toRepresentation,
    hρ.subrepresentation ρ W, ?_, ?_, F, hF, hfin, hp, hm, hcomm, hdim⟩
  · intro x
    change W.toSubmodule.mkQ x = 0 ↔ ∃ s : W.toSubmodule, s.val = x
    exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).trans
      ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨s, hs⟩ ↦ hs ▸ s.property⟩
  · intro σ
    obtain ⟨t, ht⟩ := ha σ
    exact ⟨t, fun s ↦ Subtype.ext (ht s.val)⟩
  · change (W : Set X.Points).ncard < Nat.card X.Points
    exact Set.ncard_lt_card (fun h ↦ hW.1 (SetLike.coe_injective h))

end ThreeAdicPlan
