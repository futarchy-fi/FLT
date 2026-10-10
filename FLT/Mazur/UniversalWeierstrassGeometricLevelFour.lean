/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel
public import FLT.Mazur.WeierstrassGeometricFourTorsion

/-!
# The auxiliary basis contains all geometric four-torsion

On every separably closed field point of the coefficient base, the actual
universal cubic has sixteen four-torsion points. Any faithful auxiliary basis
therefore labels all of them uniquely. This is geometric-point fullness;
finite etaleness of the torsion scheme and local existence remain separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

open AuxiliaryLevel

variable (K : Type) [Field K] [Algebra ParameterRing K]

/-- A coefficient-field point of the original universal base. -/
abbrev fieldTest : Over parameterBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ParameterRing K)))

/-- Every coefficient field has characteristic different from two. -/
theorem field_two_ne_zero : (2 : K) ≠ 0 := by
  have h := parameter_two_isUnit.map (algebraMap ParameterRing K)
  rw [map_ofNat] at h
  exact h.ne_zero

/-- The actual universal group has sixteen geometric four-torsion sections. -/
theorem geometricFourTorsion_card [IsSepClosed K] :
    Nat.card {P : fieldTest K ⟶ universalGroup // P ^ 4 = 1} = 4 ^ 2 := by
  classical
  exact WeierstrassIntegralChart.integralFourTorsion_card smoothEquation
    smoothEquation_discriminant (field_two_ne_zero K)

/-- Every geometric four-torsion section has exactly one label in a faithful auxiliary basis. -/
theorem auxiliaryMarking_geometric_full [IsSepClosed K]
    (f : fieldTest K ⟶ levelFour) (P : fieldTest K ⟶ universalGroup) (hP : P ^ 4 = 1) :
    ∃! a : Labels 4, markingOf universalGroup (Labels 4) (f ≫ auxiliaryInclusion 4) a = P := by
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  let φ := markingOf universalGroup (Labels 4) (f ≫ auxiliaryInclusion 4)
  let T := {P : fieldTest K ⟶ universalGroup // P ^ 4 = 1}
  have hc : Nat.card T = 4 ^ 2 := geometricFourTorsion_card K
  let _ : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let ψ : Labels 4 → T := fun a ↦ ⟨φ a, by rw [← map_pow, labels_pow, map_one]⟩
  have hi : Function.Injective φ := faithful_marking_injective universalGroup (Labels 4) f
  have hψ : Function.Injective ψ := fun _ _ h ↦ hi (congrArg Subtype.val h)
  have hb : Function.Bijective ψ := (Nat.bijective_iff_injective_and_card ψ).mpr
    ⟨hψ, by rw [Nat.card_eq_fintype_card, labels_card, hc]⟩
  obtain ⟨a, ha⟩ := hb.2 ⟨P, hP⟩
  refine ⟨a, congrArg Subtype.val ha, ?_⟩
  intro b hb
  exact hi (hb.trans (congrArg Subtype.val ha).symm)

end FLT.Mazur.UniversalWeierstrass
