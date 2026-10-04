/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TameInertiaCyclic
public import FLT.GaloisRepresentation.Extensions.OrdinaryInertiaExponent

/-!
# Actual exponents for a finite inertia model with prime residue field

The character is the reduction of the uniformizer ratio. Its wild kernel is a
p-group, so every prime-field line character kills that kernel. This discharges
the action obligation for this finite model. Comparison with the specified
absolute niveau-one character remains a separate ramification theorem.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions

open IsLocalRing ThreeAdicPlan SerreWeight

variable {D G : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
  [Group G] [Finite G] [MulSemiringAction G D] [FaithfulSMul G D]
  {p : ℕ} [Fact p.Prime] [CharP (ResidueField D) p]
  {π : D} (hπ : Irreducible π) (e : ResidueField D ≃+* ZMod p)

/-- The actual uniformizer character in prime-field coordinates. -/
def primeResidueInertiaCharacter : (maximalIdeal D).inertia G →* (ZMod p)ˣ :=
  (Units.map e.toMonoidHom).comp (uniformizerCharacter hπ)

/-- Every prime-field line character kills the actual wild inertia kernel. -/
theorem primeResidueInertia_kernel (χ : (maximalIdeal D).inertia G →* (ZMod p)ˣ) :
    (primeResidueInertiaCharacter hπ e).ker ≤ χ.ker := by
  have hcard : Nat.Coprime p (Nat.card (ZMod p)ˣ) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact (Nat.coprime_self_sub_right (Fact.out : p.Prime).one_le).mpr (Nat.coprime_one_right p)
  have ht := pGroup_hom_eq_one_of_coprime_card
    (uniformizerCharacter_ker_isPGroup (G := G) hπ (Fact.out : p.Prime)) hcard
    (χ.comp (uniformizerCharacter (G := G) hπ).ker.subtype)
  intro g hg
  have hu : uniformizerCharacter hπ g = 1 := by
    apply Units.ext
    apply e.injective
    have hv := congrArg Units.val hg
    change e (uniformizerCharacter hπ g : ResidueField D) = 1 at hv
    exact hv.trans (map_one e).symm
  exact DFunLike.congr_fun ht ⟨g, hu⟩

variable (hθ : Function.Surjective (primeResidueInertiaCharacter (G := G) hπ e))

/-- A normalized exponent extracted from actual finite inertia, with no kernel premise. -/
def finiteInertiaExponent (χ : (maximalIdeal D).inertia G →* (ZMod p)ˣ) : ℕ :=
  normalizedCharacterExponent (primeResidueInertiaCharacter hπ e) χ hθ
    (primeResidueInertia_kernel hπ e χ)

/-- Its normalization and the actual character identity. -/
theorem finiteInertiaExponent_spec (χ : (maximalIdeal D).inertia G →* (ZMod p)ˣ) :
    1 ≤ finiteInertiaExponent hπ e hθ χ ∧ finiteInertiaExponent hπ e hθ χ ≤ p - 1 ∧
      ∀ g, χ g = primeResidueInertiaCharacter hπ e g ^ finiteInertiaExponent hπ e hθ χ :=
  normalizedCharacterExponent_spec _ _ _ (primeResidueInertia_kernel hπ e χ)

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {ρ : Representation (ZMod p) G V} {α β : G →* (ZMod p)ˣ}
  (E : OrdinaryFiltration ρ α β)

/-- The W45 action obligation is proved for the actual finite DVR inertia model. -/
theorem ordinary_finiteInertia_action
    (g : (maximalIdeal D).inertia G) (hg : primeResidueInertiaCharacter hπ e g = 1) :
    ρ g.val (E.injection 1) = (β g.val : ZMod p) • E.injection 1 := by
  have hc := primeResidueInertia_kernel hπ e ((α / β).comp
    ((maximalIdeal D).inertia G).subtype) hg
  change α g.val / β g.val = 1 at hc
  have he := div_eq_one.mp hc
  rw [E.injection_equivariant, mul_one, he, ← map_smul, smul_eq_mul, mul_one]

include hθ E in
/-- The actual filtration therefore has its normalized ratio exponent in this model. -/
theorem ordinary_finiteInertia_exponent :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ p - 1 ∧
      ∀ g : (maximalIdeal D).inertia G,
        α g.val / β g.val = primeResidueInertiaCharacter hπ e g ^ n := by
  refine ⟨E.inertiaExponent _ _ hθ (ordinary_finiteInertia_action hπ e E), ?_⟩
  exact E.inertiaExponent_spec _ _ hθ (ordinary_finiteInertia_action hπ e E)

end GaloisRepresentation.Extensions
