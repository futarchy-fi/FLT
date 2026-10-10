/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.EllipticCurve.TorsionStructure
public import FLT.EllipticCurve.TwoTorsionCard
public import FLT.EllipticCurve.NTorsionCardOfDifferential

/-!
# Geometric bases of four-torsion

The proved counts for one-, two-, and four-torsion determine the group
structure of four-torsion. This constructs a basis in characteristic different
from two, including characteristic three, using only the explicit division
identities at two and four.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassGeometricFourBasis

variable {K : Type} [Field K] [DecidableEq K] [IsSepClosed K]
  (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0)

/-- The additive subgroup and the pointwise torsion condition count the same points. -/
def torsionPointsEquiv (d : ℕ) :
    Submodule.torsionBy ℤ W.toAffine.Point d ≃ {P : W.toAffine.Point // d • P = 0} where
  toFun P := ⟨P.val, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul]
    using P.property⟩
  invFun P := ⟨P.val, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul]
    using P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include h2

/-- All divisors of four have the required geometric torsion cardinality. -/
theorem divisor_card (d : ℕ) (hd : d ∣ 4) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point d) = d ^ 2 := by
  rw [Nat.card_congr (torsionPointsEquiv W d)]
  have hle : d ≤ 4 := Nat.le_of_dvd (by decide) hd
  interval_cases d
  · norm_num at hd
  · have : Subsingleton {P : W.toAffine.Point // 1 • P = 0} :=
      ⟨fun P Q ↦ Subtype.ext (by
        have hP : P.val = 0 := by simpa only [one_nsmul] using P.property
        have hQ : Q.val = 0 := by simpa only [one_nsmul] using Q.property
        exact hP.trans hQ.symm)⟩
    have : Nonempty {P : W.toAffine.Point // 1 • P = 0} := ⟨⟨0, by simp⟩⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  · exact W.card_two_torsion h2
  · norm_num at hd
  · have h4 : (4 : K) ≠ 0 := by
      simpa only [show (4 : K) = 2 ^ 2 by ring] using pow_ne_zero 2 h2
    exact W.card_torsion_of_divisionDifferentialDefect h4 W.divisionDifferentialDefect_four

/-- The actual geometric four-torsion group is the product of two cyclic groups of order four. -/
theorem basis :
    Nonempty (Submodule.torsionBy ℤ W.toAffine.Point (4 : ℕ) ≃+ (ZMod 4 × ZMod 4)) := by
  obtain ⟨e⟩ : Nonempty (Submodule.torsionBy ℤ W.toAffine.Point (4 : ℕ) ≃+ (Fin 2 → ZMod 4)) := by
    apply TorsionCardinality.equiv_of_card (by decide) 2
    · intro P
      exact Nat.cast_smul_eq_nsmul ℤ 4 P ▸ Submodule.smul_torsionBy ..
    · intro d hd
      rw [Nat.card_congr (TorsionCardinality.nested (A := W.toAffine.Point) hd).toEquiv]
      exact divisor_card W h2 d hd
  exact ⟨e.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

/-- A geometric basis supplies an injective marking of the original elliptic point group. -/
theorem exists_injective_marking :
    ∃ φ : (ZMod 4 × ZMod 4) →+ W.toAffine.Point, Function.Injective φ := by
  obtain ⟨e⟩ := basis W h2
  exact ⟨(Submodule.torsionBy ℤ W.toAffine.Point (4 : ℕ)).subtype.toAddMonoidHom.comp
    e.symm.toAddMonoidHom, Subtype.val_injective.comp e.symm.injective⟩

end FLT.Mazur.WeierstrassGeometricFourBasis
