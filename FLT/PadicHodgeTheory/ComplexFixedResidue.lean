/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexInvariantOrder

/-! # Fixed residues and scalar subtraction in the original de Rham ring -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The original ring action fixes any integral representative of a fixed field element. -/
theorem complexDeRham_integral_fixed_iff (a : ComplexBDeRhamPlus p) :
    (∀ σ : PadicGalois p, σ • algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) a =
      algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) a) ↔
    ∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a := by
  simp only [complexDeRhamField_smul_algebraMap, (complexDeRhamToField_injective p).eq_iff]

/-- The residue of an actual integral invariant descends uniquely to Q_p. -/
theorem complexDeRham_fixed_residue_existsUnique_scalar (a : ComplexBDeRhamPlus p)
    (ha : ∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a) :
    ∃! q : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] q = complexDeRhamTheta p a := by
  apply complexGalois_fixed_existsUnique_scalar p
  intro σ
  rw [← complexDeRhamTheta_equivariant, ha σ]

/-- Positive-order integral invariants vanish: a nonzero invariant would be a unit. -/
theorem complexDeRham_fixed_residue_zero (a : ComplexBDeRhamPlus p)
    (ha : ∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a)
    (hzero : complexDeRhamTheta p a = 0) : a = 0 := by
  by_contra hne
  have hfield : algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) a ≠ 0 :=
    (map_ne_zero_iff _ (complexDeRhamToField_injective p)).mpr hne
  obtain ⟨u, hu⟩ := complexDeRham_fixed_exists_unit p hfield
    ((complexDeRham_integral_fixed_iff p a).mpr ha)
  have hua := complexDeRhamToField_injective p hu
  exact (u.isUnit.map (complexDeRhamTheta p)).ne_zero (hua ▸ hzero)

/-- Subtracting the descended residue scalar preserves invariance and kills the residue. -/
theorem complexDeRham_fixed_scalar_subtraction (a : ComplexBDeRhamPlus p)
    (ha : ∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a)
    (q : ℚ_[p]) (hq : algebraMap ℚ_[p] ℂ_[p] q = complexDeRhamTheta p a) :
    (∀ σ : PadicGalois p,
      complexDeRhamGalois p σ (a - complexPadicToDeRham p q) =
        a - complexPadicToDeRham p q) ∧
      complexDeRhamTheta p (a - complexPadicToDeRham p q) = 0 := by
  constructor
  · intro σ
    rw [map_sub, ha σ, complexPadicToDeRham_galois]
  · rw [map_sub, complexPadicToDeRham_theta, hq, sub_self]

/-- An integral invariant equals the original scalar with its descended residue. -/
theorem complexDeRham_fixed_eq_residue_scalar (a : ComplexBDeRhamPlus p)
    (ha : ∀ σ : PadicGalois p, complexDeRhamGalois p σ a = a)
    (q : ℚ_[p]) (hq : algebraMap ℚ_[p] ℂ_[p] q = complexDeRhamTheta p a) :
    a = complexPadicToDeRham p q := by
  obtain ⟨hfix, hzero⟩ := complexDeRham_fixed_scalar_subtraction p a ha q hq
  exact sub_eq_zero.mp (complexDeRham_fixed_residue_zero p _ hfix hzero)

end PadicHodgeTheory
