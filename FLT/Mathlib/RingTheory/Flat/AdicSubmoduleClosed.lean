/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Filtration

/-! # Submodules of finite Noetherian modules are adically closed -/

@[expose] public section

namespace Submodule

variable {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N]
  [IsNoetherianRing S] [Module.Finite S N]

/-- Krull intersection applied to a quotient says that every submodule is
closed for an ideal contained in the Jacobson radical. -/
theorem mem_of_forall_mem_sup_pow_smul (P : Submodule S N) (I : Ideal S)
    (hI : I ≤ Ideal.jacobson ⊥) {x : N}
    (hx : ∀ n : ℕ, x ∈ P ⊔ I ^ n • (⊤ : Submodule S N)) : x ∈ P := by
  have hsep := I.iInf_pow_smul_eq_bot_of_le_jacobson (M := N ⧸ P) hI
  have hmem : P.mkQ x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule S (N ⧸ P)) := by
    simp only [Submodule.mem_iInf]
    intro n
    have h := Submodule.mem_map_of_mem (hx n) (f := P.mkQ)
    simpa [Submodule.map_sup, Submodule.map_smul''] using h
  have hz : P.mkQ x = 0 := by simpa [hsep] using hmem
  exact Submodule.Quotient.mk_eq_zero _ |>.mp hz

end Submodule
