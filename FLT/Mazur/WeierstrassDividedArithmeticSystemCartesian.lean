/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem

/-!
# The original arithmetic quotient system is Cartesian

Every transition, including nonadjacent orders, is the actual base change of
the integral resolved model. This retains the original coefficient spectrum
and integral projection without assuming any polygon comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (k : ℕ) (hk : k ≤ n)
local notation "X" => finiteGlobalArithmeticSystem hπ data k hk

/-- Every arithmetic order retains the same original integral model under restriction. -/
@[reassoc] theorem finiteGlobalArithmeticSystem_map_projection {a b : ℕ} (f : a ⟶ b) :
    (X).map f ≫ finiteGlobalArithmeticProjection hπ data k hk b =
      finiteGlobalArithmeticProjection hπ data k hk a := by
  have h := (finiteGlobalArithmeticSystemProjection hπ data k hk).naturality f
  exact h.trans (Category.comp_id _)

/-- Every original quotient-order square is Cartesian over its actual coefficient map. -/
theorem finiteGlobalArithmeticSystem_map_isPullback {a b : ℕ} (f : a ⟶ b) :
    IsPullback ((X).map f) (finiteGlobalArithmeticStructure hπ data k hk a)
      (finiteGlobalArithmeticStructure hπ data k hk b) ((baseSystem R π).map f) := by
  apply IsPullback.of_right
    (h₁₂ := finiteGlobalArithmeticProjection hπ data k hk b)
    (h₂₂ := baseToIntegral R π b)
  · rw [finiteGlobalArithmeticSystem_map_projection]
    have hb := (baseIntegralStructure R π).naturality f
    have he : (baseSystem R π).map f ≫ baseToIntegral R π b = baseToIntegral R π a :=
      hb.trans (Category.comp_id _)
    rw [he]
    exact IsPullback.of_hasPullback _ _
  · exact (finiteGlobalArithmeticSystemStructure hπ data k hk).naturality f
  · exact IsPullback.of_hasPullback _ _

/-- The whole original arithmetic system is equifibered over the original quotient base. -/
theorem finiteGlobalArithmeticSystemStructure_equifibered :
    (finiteGlobalArithmeticSystemStructure hπ data k hk).Equifibered :=
  fun {_ _} f => finiteGlobalArithmeticSystem_map_isPullback hπ data k hk f

end FLT.Mazur.WeierstrassDividedDepth
