/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.FiniteInertiaExponent

/-!
# Finite coefficient characters kill the actual wild kernel

The coefficient field may be any finite field of residue characteristic p.
No identification of the DVR residue field with the prime field is needed.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions
open IsLocalRing ThreeAdicPlan

variable {p : ℕ}

/-- The multiplicative group of any finite characteristic-p field has prime-to-p order. -/
theorem finiteField_units_card_coprime (k : Type*) [Field k] [Finite k] [CharP k p] :
    Nat.Coprime p (Nat.card kˣ) := by
  classical
  let := Fintype.ofFinite k
  obtain ⟨n, hp, hn⟩ := FiniteField.card k p
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hn]
  apply (Nat.coprime_pow_left_iff n.pos p (p ^ (n : ℕ) - 1)).mp
  exact (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hp.pos)).mpr
    (Nat.coprime_one_right _)

variable {D G k : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
  [Group G] [Finite G] [MulSemiringAction G D] [FaithfulSMul G D]
  [hp : Fact p.Prime] [hD : CharP (ResidueField D) p]
  [Field k] [Finite k] [hk : CharP k p]
  {π : D} (hπ : Irreducible π)

include hp hD hk in
/-- The actual uniformizer-character kernel is killed by every finite coefficient character. -/
theorem finiteCoefficient_uniformizer_kernel
    (χ : (maximalIdeal D).inertia G →* kˣ) :
    (uniformizerCharacter hπ).ker ≤ χ.ker := by
  have h := pGroup_hom_eq_one_of_coprime_card
    (uniformizerCharacter_ker_isPGroup (G := G) hπ (Fact.out : p.Prime))
    (finiteField_units_card_coprime (p := p) k)
    (χ.comp (uniformizerCharacter (G := G) hπ).ker.subtype)
  intro g hg
  exact DFunLike.congr_fun h ⟨g, hg⟩

variable {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)

include hp hD hk in
/-- The ordinary line action obligation holds over every finite coefficient field. -/
theorem ordinary_finiteCoefficient_wild_action
    (g : (maximalIdeal D).inertia G) (hg : uniformizerCharacter hπ g = 1) :
    ρ g.val (E.injection 1) = (β g.val : k) • E.injection 1 := by
  have hc := finiteCoefficient_uniformizer_kernel (p := p) hπ
    ((α / β).comp ((maximalIdeal D).inertia G).subtype) hg
  change α g.val / β g.val = 1 at hc
  have he := div_eq_one.mp hc
  rw [E.injection_equivariant, mul_one, he, ← map_smul, smul_eq_mul, mul_one]

end GaloisRepresentation.Extensions
