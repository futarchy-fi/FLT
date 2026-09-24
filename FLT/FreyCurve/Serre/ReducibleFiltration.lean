/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.FreyCurve.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Character filtrations of reducible representations

A reducible two-dimensional representation has an invariant line and a one-dimensional
quotient. Transporting their actions to the scalar field gives an exact character filtration;
no splitting of the representation is asserted.
-/

@[expose] public section

noncomputable section

namespace GaloisRep

variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
  [DiscreteTopology k] [AddCommGroup V] [Module k V]

/-- An exact filtration by continuous characters on the standard one-dimensional space. -/
structure CharacterFiltration (ρ : GaloisRep K k V) where
  /-- The character on the invariant line. -/
  χ₁ : GaloisRep K k k
  /-- The character on the quotient line. -/
  χ₂ : GaloisRep K k k
  /-- The inclusion of the invariant line in chosen coordinates. -/
  i : k →ₗ[k] V
  /-- The quotient map in chosen coordinates. -/
  q : V →ₗ[k] k
  /-- The line inclusion is injective. -/
  i_injective : Function.Injective i
  /-- The quotient map is surjective. -/
  q_surjective : Function.Surjective q
  /-- The image of the line is exactly the kernel of the quotient. -/
  exactness : LinearMap.range i = LinearMap.ker q
  /-- The inclusion respects the Galois actions. -/
  i_equivariant : ∀ g x, ρ g (i x) = i (χ₁ g x)
  /-- The quotient map respects the Galois actions. -/
  q_equivariant : ∀ g v, q (ρ g v) = χ₂ g (q v)

/-- The module topology over a discrete field is discrete. -/
theorem moduleTopology_eq_bot : moduleTopology k V = ⊥ := by
  let : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  have : ContinuousSMul k V := ⟨continuous_of_discreteTopology⟩
  have : ContinuousAdd V := ⟨continuous_of_discreteTopology⟩
  exact le_bot_iff.mp (moduleTopology_le k V)

/-- A representation determined by a continuous discrete representation is continuous. -/
def ofDetermined {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : GaloisRep K k V) (σ : Representation k (Field.absoluteGaloisGroup K) W)
    (hσ : ∀ g h, ρ g = ρ h → σ g = σ h) : GaloisRep K k W := by
  letI := moduleTopology k (Module.End k V)
  letI := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k V) := ⟨moduleTopology_eq_bot⟩
  refine ⟨σ, IsLocallyConstant.continuous ?_⟩
  have hρ : IsLocallyConstant ρ := (IsLocallyConstant.iff_continuous _).mpr ρ.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  exact (hρ.eventually_eq g).mono fun h hh ↦ hσ h g hh

/-- Restrict a continuous representation over a discrete field to an invariant subspace. -/
def onSubrepresentation (ρ : GaloisRep K k V) (S : Subrepresentation ρ.toRepresentation) :
    GaloisRep K k S.toSubmodule :=
  ofDetermined ρ S.toRepresentation fun g h hgh ↦ by
    ext v
    exact congrArg (fun f : Module.End k V ↦ f v.val) hgh

/-- The algebraic action induced on the quotient by an invariant subspace. -/
def quotientRepresentation (ρ : GaloisRep K k V) (S : Subrepresentation ρ.toRepresentation) :
    Representation k (Field.absoluteGaloisGroup K) (V ⧸ S.toSubmodule) where
  toFun g := S.toSubmodule.mapQ S.toSubmodule (ρ g) (S.apply_mem_toSubmodule g)
  map_one' := by
    ext v
    simp [Submodule.mapQ_apply]
  map_mul' g h := by
    ext v
    change S.toSubmodule.mkQ (ρ (g * h) v) = S.toSubmodule.mkQ (ρ g (ρ h v))
    rw [map_mul]
    rfl

/-- Descend a continuous representation over a discrete field to an invariant quotient. -/
def onQuotient (ρ : GaloisRep K k V) (S : Subrepresentation ρ.toRepresentation) :
    GaloisRep K k (V ⧸ S.toSubmodule) :=
  ofDetermined ρ (quotientRepresentation ρ S) fun g h hgh ↦ by
    ext v
    change S.toSubmodule.mkQ (ρ g v) = S.toSubmodule.mkQ (ρ h v)
    rw [hgh]

/-- Every reducible representation of dimension two over a discrete field has an exact
filtration by two continuous characters. -/
theorem filtration_of_reducible (ρ : GaloisRep K k V)
    (hdim : Module.finrank k V = 2) (hred : ¬ ρ.IsIrreducible) :
    Nonempty (CharacterFiltration ρ) := by
  classical
  have : FiniteDimensional k V := FiniteDimensional.of_finrank_eq_succ hdim
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank k V)
  have : Nontrivial (Subrepresentation ρ.toRepresentation) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have : (⊥ : Submodule k V) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top this
  obtain ⟨S, hSb, hSt⟩ : ∃ S : Subrepresentation ρ.toRepresentation, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra! h
    exact hred (IsSimpleOrder.of_forall_eq_top h)
  have hSb' : S.toSubmodule ≠ ⊥ := fun h ↦ hSb (Subrepresentation.toSubmodule_injective h)
  have hSt' : S.toSubmodule ≠ ⊤ := fun h ↦ hSt (Subrepresentation.toSubmodule_injective h)
  have hS : Module.finrank k S.toSubmodule = 1 := by
    have := Submodule.finrank_lt hSt'
    have := (Submodule.finrank_eq_zero (S := S.toSubmodule)).not.mpr hSb'
    omega
  have hQ : Module.finrank k (V ⧸ S.toSubmodule) = 1 := by
    have := S.toSubmodule.finrank_quotient_add_finrank
    omega
  let e₁ : S.toSubmodule ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by simpa using hS)
  let e₂ : (V ⧸ S.toSubmodule) ≃ₗ[k] k := LinearEquiv.ofFinrankEq _ _ (by simpa using hQ)
  refine ⟨{
    χ₁ := (ρ.onSubrepresentation S).conj e₁
    χ₂ := (ρ.onQuotient S).conj e₂
    i := S.toSubmodule.subtype.comp e₁.symm.toLinearMap
    q := e₂.toLinearMap.comp S.toSubmodule.mkQ
    i_injective := Subtype.val_injective.comp e₁.symm.injective
    q_surjective := e₂.surjective.comp S.toSubmodule.mkQ_surjective
    exactness := ?_
    i_equivariant := ?_
    q_equivariant := ?_ }⟩
  · ext v
    simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      have hv : v ∈ S.toSubmodule := by simpa using h
      exact ⟨e₁ ⟨v, hv⟩, by simp⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conj_apply_apply,
      LinearEquiv.symm_apply_apply]
    rfl
  · intro g v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conj_apply_apply,
      LinearEquiv.symm_apply_apply]
    rfl

end GaloisRep

namespace WeierstrassCurve

/-- Reducible prime torsion of an elliptic curve over `ℚ` has an exact character filtration.

The linear-algebra construction is independent of elliptic-curve axioms. This specialization
uses the existing torsion-dimension theorem, which depends on `n_torsion_card` and
`group_theory_lemma`, both currently admitted in `FLT.EllipticCurve.Torsion`.
-/
theorem filtration_of_reducible (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp : 0 < p)
    (hred : ¬ (E.galoisRep p hp).IsIrreducible) :
    Nonempty (GaloisRep.CharacterFiltration (E.galoisRep p hp)) := by
  obtain ⟨e⟩ := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_dimension
    (n := p) (by exact_mod_cast (Nat.ne_of_gt hp))
  let e' : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p ≃ₗ[ZMod p]
      ZMod p × ZMod p :=
    { e with map_smul' := ZMod.map_smul e }
  apply GaloisRep.filtration_of_reducible _ _ hred
  rw [e'.finrank_eq, Module.finrank_prod]
  simp

end WeierstrassCurve

/-- The Serre bridge's character-filtration leaf for the Frey curve.

This inherits the existing torsion-dimension admissions documented in
`WeierstrassCurve.filtration_of_reducible`.
-/
theorem FreyPackage.filtration_of_reducible (P : FreyPackage) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    ¬ (P.freyCurve.galoisRep P.p P.hppos).IsIrreducible →
      Nonempty (GaloisRep.CharacterFiltration (P.freyCurve.galoisRep P.p P.hppos)) := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact P.freyCurve.filtration_of_reducible P.p P.hppos
