/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltration
public import FLT.GaloisRepresentation.SerreWeight.NormalizedCharacterExponent

/-!
# Normalizing the inertia ratio of an actual ordinary filtration

The factorization obligation is stated on the action of the middle
representation on its injected line. It supplies a normalized exponent, not
a numerical Serre weight. Proving the obligation for a specific arithmetic
representation still requires its ramification theory.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions.OrdinaryFiltration

open SerreWeight

variable {G V : Type*} [Group G] {p : ℕ} [Fact p.Prime]
  [AddCommGroup V] [Module (ZMod p) V]
  {ρ : Representation (ZMod p) G V} {α β : G →* (ZMod p)ˣ}
  (E : OrdinaryFiltration ρ α β) (I : Subgroup G)
  (θ : I →* (ZMod p)ˣ)
  (hθ : Function.Surjective θ)
  (haction : ∀ g : I, θ g = 1 → ρ g.val (E.injection 1) =
    (β g.val : ZMod p) • E.injection 1)

/-- The quotient-normalized character of the actual two lines on inertia. -/
def inertiaRatio : I →* (ZMod p)ˣ := (α / β).comp I.subtype

include haction in
/-- The action obligation implies factorization through the specified inertia character. -/
theorem inertiaRatio_kernel : θ.ker ≤ (inertiaRatio (α := α) (β := β) I).ker := by
  intro g hg
  have h := haction g hg
  rw [E.injection_equivariant, mul_one, ← map_smul, smul_eq_mul, mul_one] at h
  have he : α g.val = β g.val := Units.ext (E.injective h)
  change α g.val / β g.val = 1
  simp [he]

/-- The normalized inertia exponent is constructed from the actual filtered action. -/
def inertiaExponent : ℕ :=
  normalizedCharacterExponent θ (inertiaRatio (α := α) (β := β) I) hθ
    (E.inertiaRatio_kernel I θ haction)

/-- Its range and power relation are proved from that action. -/
theorem inertiaExponent_spec :
    1 ≤ E.inertiaExponent I θ hθ haction ∧
      E.inertiaExponent I θ hθ haction ≤ p - 1 ∧
      ∀ g : I, α g.val / β g.val = θ g ^ E.inertiaExponent I θ hθ haction :=
  normalizedCharacterExponent_spec θ (inertiaRatio (α := α) (β := β) I) hθ
    (E.inertiaRatio_kernel I θ haction)

/-- Equal inertial line characters give exponent p-1 even for nonsplit extensions. -/
theorem inertiaExponent_scalar_iff :
    E.inertiaExponent I θ hθ haction = p - 1 ↔ ∀ g : I, α g.val = β g.val := by
  rw [inertiaExponent, normalizedCharacterExponent_eq_card_sub_one_iff]
  constructor
  · intro h g
    have he := DFunLike.congr_fun h g
    change α g.val / β g.val = 1 at he
    exact div_eq_one.mp he
  · intro h
    apply MonoidHom.ext
    intro g
    change α g.val / β g.val = 1
    simp [h]

end GaloisRepresentation.Extensions.OrdinaryFiltration
