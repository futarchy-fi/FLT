/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleFactorCharacter

/-!
# Binary weights of original two-dimensional inertia factors

The scalar model, integral lifts, scalar character and residue embedding
are constructed from the original simple factor before applying local weights.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing RaynaudParameters

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "I" => localInertiaGroup v
local notation "Rsh" => unramifiedUnion (Ω := Ωv) (p : O)
local notation "Lsh" => FractionRing Rsh
local notation "Av" => IntegralClosure O Ωv

/-- Retain the canonical fraction-ring base algebra in the completion-field tower. -/
local instance twoWeightBaseAlgebra : Algebra O Lsh := inferInstance
variable [Algebra (v.adicCompletion K) (FractionRing (unramifiedUnion
    (Ω := AlgebraicClosure (v.adicCompletion K)) (p : v.adicCompletionIntegers K)))]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K)
    (FractionRing (unramifiedUnion (Ω := AlgebraicClosure (v.adicCompletion K))
      (p : v.adicCompletionIntegers K)))]
  [HenselianLocalRing (v.adicCompletionIntegers K)]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K))
  {U W : Type} [AddCommGroup U] [AddCommGroup W]
  [DistribMulAction (localInertiaGroup v) U] [DistribMulAction (localInertiaGroup v) W]
  [Module (ZMod p) W]
  (ρ : Representation (ZMod p) (localInertiaGroup v) W) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) W)ˣ] [DiscreteTopology (Module.End (ZMod p) W)ˣ]

-- The constructed tower and nested scalar-model witnesses require extra elaboration.
set_option synthInstance.maxHeartbeats 100000 in
-- The canonical fraction-ring scalar instances need a larger search budget.
set_option maxHeartbeats 1600000 in
-- Constructing and comparing the nested local models requires extra elaboration.
/-- An original rank-two prime-field factor has a binary fundamental-character weight. -/
theorem exists_original_two_weight (hp : Irreducible (p : O))
    (hρ : Continuous ρ.toHomUnits) (hact : ∀ σ w, ρ σ w = σ • w)
    (i : U →+[I] X.Points) (q : U →+[I] W)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hdimW : Module.finrank (ZMod p) W = 2)
    (e : Lsh →ₐ[Kv] Ωv) (he : ∀ a : Rsh, e (algebraMap Rsh Lsh a) = (a : Ωv))
    {α : Ωv} (hn : 0 < p * p - 1) (hp0 : (p : Kv) ≠ 0)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ωv (p : Kv)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F W)
      (χ : I →* Fˣ) (ε : F →+* ResidueField Av) (a b : ℕ),
      Module.finrank F W = 1 ∧ a ≤ 1 ∧ b ≤ 1 ∧ (∀ (σ : I) (w : W), σ • w = (χ σ : F) • w) ∧
      ∀ σ : I, ε (χ σ) = (LocalRoot.character v hn hp0 hα σ : ResidueField Av) ^ (p * a + b) := by
  classical
  let : Algebra O Lsh := inferInstance
  let : Algebra Rsh Lsh := inferInstance
  let : SMul Rsh Lsh := (inferInstance : Algebra Rsh Lsh).toSMul
  let : SMul O Lsh := (inferInstance : Algebra O Lsh).toSMul
  let : IsScalarTower O Rsh Lsh := .of_algebraMap_eq fun _ ↦ rfl
  let : IsDiscreteValuationRing Rsh := unramifiedUnion_dvr hp
  let : HenselianLocalRing Rsh := unramifiedUnion_henselian hp
  let : IsSepClosed (ResidueField Rsh) := unramifiedUnion_residue_isSepClosed hp
  let : Algebra.IsIntegral O Rsh := unramifiedUnion_integral hp
  let : FaithfulSMul O Rsh := (faithfulSMul_iff_algebraMap_injective O Rsh).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective O Ωv (congrArg Subtype.val h))
  let : IsLocalHom (algebraMap O Rsh) := inferInstance
  let : CharP (ResidueField Rsh) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField O) (ResidueField Rsh)).injective p
  let : CharZero Lsh := charZero_of_injective_algebraMap (algebraMap Kv Lsh).injective
  obtain ⟨F, hF, hfin, hchar, hmod, χ, M, hmodM, _f, lift, hdim, hdimM,
    hχ, hχM, hlift, h0, h1, hadd, hmul⟩ :=
    exists_simple_factor_character_model v hp X p ρ hρ hact i q hi hq e he
  let : Fintype F := Fintype.ofFinite F
  let : Finite U := Finite.of_injective i hi
  let : Finite W := Finite.of_surjective q hq
  let : Fintype W := Fintype.ofFinite W
  have hcard : Fintype.card F = p ^ (2 : ℕ) := by
    let b : F ≃ₗ[F] W := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some
    rw [Fintype.card_congr b.toEquiv, Module.card_eq_pow_finrank (K := ZMod p),
      ZMod.card, hdimW]
  obtain ⟨ε⟩ := exists_scalar_residue_embedding (R := Rsh) (F := F) p
  obtain ⟨_, hu, _⟩ := henselian_group_characters (R := Rsh) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  let : Invertible (Fintype.card Fˣ : Rsh) := hu.invertible
  let basis : F ≃ₗ[F] M.Points := (Module.nonempty_linearEquiv_of_finrank_eq_one hdimM).some
  have hbasis : basis 1 ≠ 0 := fun h ↦
    one_ne_zero (basis.injective (h.trans basis.map_zero.symm))
  have hpR : Irreducible (p : Rsh) := by
    simpa only [map_natCast] using unramifiedUnion_uniformizer (Ω := Ωv) hp
  obtain ⟨a, b, ha, hb, hw⟩ := M.two_cycle_scalar_weight (K := K) (R := Rsh) (L := Lsh) (F := F)
    v lift h0 h1 hmul hadd p hdimM hlift
    ε e hpR hcard (basis 1) hbasis hn hp0 hα
  refine ⟨F, hF, hfin, hchar, hmod, χ, (towerResidueMap (R := Rsh) (L := Lsh) v e).comp ε,
     a, b, hdim, ha, hb, hχ, ?_⟩
  intro σ
  exact hw σ (inertia_fixes_fractionField v (e.restrictScalars O) he σ) (χ σ) (hχM σ (basis 1))

end ThreeAdicPlan
