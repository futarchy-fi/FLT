/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The kernel of reduction of a submodule inclusion

Reduction need not preserve an inclusion. The reduced inclusion below retains
its actual kernel; injectivity is precisely the intersection identity needed
to turn ambient ideal membership into divisibility inside the submodule.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SubmoduleReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (Q : Submodule R M)

/-- The inclusion of a submodule, reduced modulo the same scalar ideal on both sides. -/
def inclusion : (Q ⧸ J • (⊤ : Submodule R Q)) →ₗ[R]
    M ⧸ J • (⊤ : Submodule R M) :=
  (J • (⊤ : Submodule R Q)).mapQ (J • (⊤ : Submodule R M)) Q.subtype
    (Submodule.smul_top_le_comap_smul_top J Q.subtype)

/-- Reduction of an actual submodule element is reduction of its ambient value. -/
theorem inclusion_mk (x : Q) :
    inclusion J Q ((J • (⊤ : Submodule R Q)).mkQ x) =
      (J • (⊤ : Submodule R M)).mkQ x.val := rfl

/-- The kernel records the intersection with the ambient ideal multiple. -/
theorem ker_inclusion :
    LinearMap.ker (inclusion J Q) =
      ((J • (⊤ : Submodule R M)).comap Q.subtype).map
        (J • (⊤ : Submodule R Q)).mkQ :=
  Submodule.ker_mapQ _ _ _ _

/-- Injectivity holds exactly when ambient ideal multiples in Q are internal multiples. -/
theorem inclusion_injective_iff : Function.Injective (inclusion J Q) ↔
    Q ⊓ J • (⊤ : Submodule R M) = J • Q := by
  rw [← LinearMap.ker_eq_bot, ker_inclusion, ← le_bot_iff, Submodule.map_le_iff_le_comap,
    Submodule.comap_bot, Submodule.ker_mkQ]
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      exact (Submodule.mem_smul_top_iff J Q ⟨x, hx.1⟩).mp (h hx.2)
    · exact le_inf Submodule.smul_le_right (smul_mono_right J le_top)
  · intro h x hx
    apply (Submodule.mem_smul_top_iff J Q x).mpr
    rw [← h]
    exact ⟨x.property, hx⟩

/-- Under injective reduction, ambient vanishing gives genuine internal divisibility. -/
theorem le_smul_of_inclusion_injective
    (hinj : Function.Injective (inclusion J Q))
    (hzero : Q ≤ J • (⊤ : Submodule R M)) : Q ≤ J • Q := by
  rw [← (inclusion_injective_iff J Q).mp hinj]
  exact le_inf le_rfl hzero

end FLT.Mazur.SubmoduleReduction
