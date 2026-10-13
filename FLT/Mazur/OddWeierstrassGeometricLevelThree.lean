/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryLevel
public import FLT.Mazur.WeierstrassGeometricThreeTorsion

/-!
# The auxiliary basis contains all geometric three-torsion

On every separably closed field point of the coefficient base, the actual
universal cubic has nine three-torsion points. Any faithful auxiliary basis
therefore labels all of them uniquely. This is geometric-point fullness;
finite etaleness of the torsion scheme and local existence remain separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OddWeierstrassParameter

open AuxiliaryLevel
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant
  oddChart_three_isUnit)
open UniversalWeierstrass (Labels labels_pow labels_card)

variable (K : Type) [Field K] [Algebra OddChartRing K]

/-- A coefficient-field point of the original universal base. -/
abbrev fieldTest : Over parameterBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap OddChartRing K)))

/-- Every coefficient field has characteristic different from three. -/
theorem field_three_ne_zero : (3 : K) ≠ 0 := by
  have h := oddChart_three_isUnit.map (algebraMap OddChartRing K)
  rw [map_ofNat] at h
  exact h.ne_zero

/-- The actual universal group has nine geometric three-torsion sections. -/
theorem geometricThreeTorsion_card [IsSepClosed K] :
    Nat.card {P : fieldTest K ⟶ universalGroup // P ^ 3 = 1} = 3 ^ 2 := by
  classical
  exact WeierstrassIntegralChart.integralThreeTorsion_card oddChartEquation
    oddChart_discriminant (field_three_ne_zero K)

/-- Every geometric three-torsion section has exactly one label in a faithful auxiliary basis. -/
theorem levelThreeMarking_geometric_full [IsSepClosed K]
    (f : fieldTest K ⟶ levelThree) (P : fieldTest K ⟶ universalGroup) (hP : P ^ 3 = 1) :
    ∃! a : Labels 3, markingOf universalGroup (Labels 3) (f ≫ levelThreeInclusion) a = P := by
  let _ : Nonempty (fieldTest K).left := ⟨IsLocalRing.closedPoint K⟩
  let φ := markingOf universalGroup (Labels 3) (f ≫ levelThreeInclusion)
  let T := {P : fieldTest K ⟶ universalGroup // P ^ 3 = 1}
  have hc : Nat.card T = 3 ^ 2 := geometricThreeTorsion_card K
  let _ : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let ψ : Labels 3 → T := fun a ↦ ⟨φ a, by rw [← map_pow, labels_pow, map_one]⟩
  have hi : Function.Injective φ := faithful_marking_injective universalGroup (Labels 3) f
  have hψ : Function.Injective ψ := fun _ _ h ↦ hi (congrArg Subtype.val h)
  have hb : Function.Bijective ψ := (Nat.bijective_iff_injective_and_card ψ).mpr
    ⟨hψ, by rw [Nat.card_eq_fintype_card, labels_card, hc]⟩
  obtain ⟨a, ha⟩ := hb.2 ⟨P, hP⟩
  refine ⟨a, congrArg Subtype.val ha, ?_⟩
  intro b hb
  exact hi (hb.trans (congrArg Subtype.val ha).symm)

end FLT.Mazur.OddWeierstrassParameter
