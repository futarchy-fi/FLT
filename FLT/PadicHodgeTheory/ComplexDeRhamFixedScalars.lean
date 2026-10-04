/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFixedResidue

/-! # The fixed field of the original de Rham period field is Q_p -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Every fixed element of the original period field descends to a unique original Q_p scalar. -/
theorem complexDeRham_fixed_existsUnique_scalar (x : ComplexBDeRham p)
    (hx : ∀ σ : PadicGalois p, σ • x = x) :
    ∃! q : ℚ_[p], complexPadicToDeRhamField p q = x := by
  obtain ⟨a, rfl⟩ := complexDeRham_fixed_exists_integral p x hx
  have ha := (complexDeRham_integral_fixed_iff p a).mp hx
  obtain ⟨q, hq, _⟩ := complexDeRham_fixed_residue_existsUnique_scalar p a ha
  have he := complexDeRham_fixed_eq_residue_scalar p a ha q hq
  refine ⟨q, ?_, ?_⟩
  · change algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexPadicToDeRham p q) = _
    rw [he]
  · intro b hb
    apply complexPadicToDeRhamField_injective p
    exact hb.trans (congrArg (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)) he)

/-- The fixed elements of B_dR are exactly the image of the original Q_p embedding. -/
theorem complexDeRham_fixed_iff_mem_range (x : ComplexBDeRham p) :
    (∀ σ : PadicGalois p, σ • x = x) ↔ x ∈ Set.range (complexPadicToDeRhamField p) := by
  constructor
  · intro hx
    obtain ⟨q, hq, _⟩ := complexDeRham_fixed_existsUnique_scalar p x hx
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩ σ
    exact complexPadicToDeRhamField_fixed p σ q

/-- The integral period ring has the same fixed scalars under its original action. -/
theorem complexDeRhamPlus_fixed_iff_mem_range (a : ComplexBDeRhamPlus p) :
    (∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a) ↔
      a ∈ Set.range (complexPadicToDeRham p) := by
  constructor
  · intro ha
    obtain ⟨q, hq, _⟩ := complexDeRham_fixed_residue_existsUnique_scalar p a ha
    exact ⟨q, (complexDeRham_fixed_eq_residue_scalar p a ha q hq).symm⟩
  · rintro ⟨q, rfl⟩ σ
    exact complexPadicToDeRham_galois p σ q

end PadicHodgeTheory
