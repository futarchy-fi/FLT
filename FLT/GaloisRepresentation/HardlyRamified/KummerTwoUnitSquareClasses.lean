/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoClassNumber
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Bounding unit square classes

Dirichlet's theorem and cyclicity of the torsion subgroup bound the number of
unit square classes in the sextic Kummer field by eight.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

open NumberField

/-- Three binary powers in a commutative group. -/
def binaryTripleProduct {G : Type*} [CommGroup G] (x y z : G)
    (e : Fin 2 × Fin 2 × Fin 2) : G := x ^ e.1.val * y ^ e.2.1.val * z ^ e.2.2.val

/-- Triviality of the binary kernel proves independence of three elements of exponent two. -/
theorem binaryTripleProduct_injective {G : Type*} [CommGroup G]
    (hpow : ∀ g : G, g ^ 2 = 1) (x y z : G)
    (hker : ∀ e, binaryTripleProduct x y z e = 1 → e = (0, 0, 0)) :
    Function.Injective (binaryTripleProduct x y z) := by
  intro e f hef
  let d : Fin 2 × Fin 2 × Fin 2 :=
    (⟨(e.1.val + f.1.val) % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(e.2.1.val + f.2.1.val) % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(e.2.2.val + f.2.2.val) % 2, Nat.mod_lt _ (by decide)⟩)
  have hd : binaryTripleProduct x y z d = 1 := by
    calc
      binaryTripleProduct x y z d =
          binaryTripleProduct x y z e * binaryTripleProduct x y z f := by
        dsimp [binaryTripleProduct, d]
        rw [← pow_eq_pow_mod _ (hpow x), ← pow_eq_pow_mod _ (hpow y),
          ← pow_eq_pow_mod _ (hpow z)]
        simp only [pow_add]
        ac_rfl
      _ = binaryTripleProduct x y z f ^ 2 := by rw [hef, pow_two]
      _ = 1 := hpow _
  have hd0 := hker d hd
  have h1 := congrArg (fun b : Fin 2 × Fin 2 × Fin 2 ↦ b.1.val) hd0
  have h2 := congrArg (fun b : Fin 2 × Fin 2 × Fin 2 ↦ b.2.1.val) hd0
  have h3 := congrArg (fun b : Fin 2 × Fin 2 × Fin 2 ↦ b.2.2.val) hd0
  dsimp [d] at h1 h2 h3
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

/-- Integer powers of an element of exponent two have a binary representative. -/
theorem exists_binary_pow_eq_zpow {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1)
    (n : ℤ) : ∃ i : Fin 2, g ^ n = g ^ i.val := by
  have hnonneg : 0 ≤ n % 2 := Int.emod_nonneg _ (by decide)
  have hlt : n % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  refine ⟨⟨(n % 2).toNat, by omega⟩, ?_⟩
  rw [zpow_eq_zpow_emod' n hg, ← zpow_natCast]
  congr 1
  change n % 2 = ((n % 2).toNat : ℤ)
  omega

/-- The unit rank of the sextic Kummer field is two. -/
theorem unit_rank_kummerTwoField : NumberField.Units.rank K₀ = 2 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_kummerTwoField, nrComplexPlaces_kummerTwoField]

/-- The quotient of units by their squares. -/
abbrev KummerTwoUnitSquareClasses :=
  (𝓞 K₀)ˣ ⧸ (powMonoidHom (α := (𝓞 K₀)ˣ) 2).range

/-- Unit square classes have exponent dividing two. -/
theorem kummerTwoUnitSquareClasses_sq (q : KummerTwoUnitSquareClasses) : q ^ 2 = 1 := by
  refine QuotientGroup.induction_on q ?_
  intro u
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

/-- There are at most eight unit square classes. No particular fundamental units are needed. -/
theorem card_kummerTwoUnitSquareClasses_le : Nat.card KummerTwoUnitSquareClasses ≤ 8 := by
  classical
  let f := QuotientGroup.mk' (powMonoidHom (α := (𝓞 K₀)ˣ) 2).range
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion K₀)
  let g : Fin 2 × (Fin (NumberField.Units.rank K₀) → Fin 2) →
      KummerTwoUnitSquareClasses := fun b ↦
    f ζ.val ^ b.1.val * ∏ i, f (NumberField.Units.fundSystem K₀ i) ^ (b.2 i).val
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨⟨ξ, e⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K₀ u
    obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).mp (hζ ξ)
    obtain ⟨b, hb⟩ := exists_binary_pow_eq_zpow (f ζ.val)
      (kummerTwoUnitSquareClasses_sq _) n
    choose c hc using fun i ↦ exists_binary_pow_eq_zpow (f (NumberField.Units.fundSystem K₀ i))
      (kummerTwoUnitSquareClasses_sq _) (e i)
    refine ⟨(b, c), ?_⟩
    change f ζ.val ^ b.val * ∏ i, f (NumberField.Units.fundSystem K₀ i) ^ (c i).val = f u
    rw [hu, map_mul, map_prod]
    have hξ : ξ.val = ζ.val ^ n := congrArg Subtype.val hn.symm
    rw [hξ, map_zpow, hb]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [map_zpow, hc]
  have hcard := Nat.card_le_card_of_surjective g hsurj
  simpa [Nat.card_prod, Nat.card_fun, Nat.card_fin, unit_rank_kummerTwoField] using hcard

instance : Finite KummerTwoUnitSquareClasses := by
  let := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K₀)ˣ (by decide : 2 ≠ 0)
  infer_instance

end ThreeAdicPlan
