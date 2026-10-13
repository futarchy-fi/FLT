/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassGeometricFourBasis

/-!
# Geometric bases of three-torsion

The proved counts for one- and three-torsion determine the group
structure of three-torsion. This constructs a basis in characteristic different
from three, including characteristic two, using only the explicit division
identities at three.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassGeometricThreeBasis

variable {K : Type} [Field K] [DecidableEq K] [IsSepClosed K]
  (W : WeierstrassCurve K) [W.IsElliptic] (h3 : (3 : K) ≠ 0)

include h3

/-- All divisors of three have the required geometric torsion cardinality. -/
theorem divisor_card (d : ℕ) (hd : d ∣ 3) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point d) = d ^ 2 := by
  rw [Nat.card_congr (WeierstrassGeometricFourBasis.torsionPointsEquiv W d)]
  have hle : d ≤ 3 := Nat.le_of_dvd (by decide) hd
  interval_cases d
  · norm_num at hd
  · have : Subsingleton {P : W.toAffine.Point // 1 • P = 0} :=
      ⟨fun P Q ↦ Subtype.ext (by
        have hP : P.val = 0 := by simpa only [one_nsmul] using P.property
        have hQ : Q.val = 0 := by simpa only [one_nsmul] using Q.property
        exact hP.trans hQ.symm)⟩
    have : Nonempty {P : W.toAffine.Point // 1 • P = 0} := ⟨⟨0, by simp⟩⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  · norm_num at hd
  · exact W.card_torsion_of_divisionDifferentialDefect h3 W.divisionDifferentialDefect_three

/-- The actual geometric three-torsion group is the product of two cyclic groups of order three. -/
theorem basis :
    Nonempty (Submodule.torsionBy ℤ W.toAffine.Point (3 : ℕ) ≃+ (ZMod 3 × ZMod 3)) := by
  obtain ⟨e⟩ : Nonempty (Submodule.torsionBy ℤ W.toAffine.Point (3 : ℕ) ≃+ (Fin 2 → ZMod 3)) := by
    apply TorsionCardinality.equiv_of_card (by decide) 2
    · intro P
      exact Nat.cast_smul_eq_nsmul ℤ 3 P ▸ Submodule.smul_torsionBy ..
    · intro d hd
      rw [Nat.card_congr (TorsionCardinality.nested (A := W.toAffine.Point) hd).toEquiv]
      exact divisor_card W h3 d hd
  exact ⟨e.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

/-- A geometric basis supplies an injective marking of the original elliptic point group. -/
theorem exists_injective_marking :
    ∃ φ : (ZMod 3 × ZMod 3) →+ W.toAffine.Point, Function.Injective φ := by
  obtain ⟨e⟩ := basis W h3
  exact ⟨(Submodule.torsionBy ℤ W.toAffine.Point (3 : ℕ)).subtype.toAddMonoidHom.comp
    e.symm.toAddMonoidHom, Subtype.val_injective.comp e.symm.injective⟩

end FLT.Mazur.WeierstrassGeometricThreeBasis
