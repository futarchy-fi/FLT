/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteFlat
public import FLT.Mazur.WeierstrassDividedGlobalFiniteZero
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Flatness of the whole finite projective models

The finite local model and the original chart at infinity form an actual
open cover. Both retain flat structure maps, so every whole finite model
is flat. Over a Noetherian base its arbitrary base changes are open quotients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The unchanged infinity chart retains its original base structure morphism. -/
@[reassoc] theorem finiteInfinityChart_structure :
    finiteInfinityChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      chartStructure W 1 := by
  rw [finiteGlobalStructure, finiteInfinityChart_contraction_assoc, integralCurveChart_structure]

/-- The finite local chart retains the already constructed flat structure morphism. -/
@[reassoc] theorem finiteLocalChart_structure :
    finiteLocalChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      finiteStructure hπ data j hj := by
  rw [finiteGlobalStructure, finiteLocalChart_contraction_assoc]
  rfl

/-- Every whole finite projective model is flat over the original Bezout domain. -/
instance finiteGlobalStructure_flat : Flat (finiteGlobalStructure hπ data j hj) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (SchemeOpenReplacement.targetCover (affineBoundaryToY W) (finiteYBoundary hπ data j hj))
  intro i
  cases i with
  | false =>
    change Flat (finiteInfinityChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj)
    rw [finiteInfinityChart_structure]
    infer_instance
  | true =>
    change Flat (finiteLocalChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj)
    rw [finiteLocalChart_structure]
    infer_instance

variable [IsNoetherianRing R]

/-- The whole proper flat family is universally open over a Noetherian base. -/
instance finiteGlobalStructure_universallyOpen :
    UniversallyOpen (finiteGlobalStructure hπ data j hj) := UniversallyOpen.of_flat _

/-- Every base change of the whole finite family is an open quotient onto its base. -/
theorem finiteGlobalBaseChange_openQuotient {S : Scheme.{u}} (f : S ⟶ Spec (.of R)) :
    IsOpenQuotientMap (pullback.snd (finiteGlobalStructure hπ data j hj) f) :=
  ⟨(pullback.snd (finiteGlobalStructure hπ data j hj) f).surjective,
    (pullback.snd (finiteGlobalStructure hπ data j hj) f).continuous,
    (pullback.snd (finiteGlobalStructure hπ data j hj) f).isOpenMap⟩

end FLT.Mazur.WeierstrassDividedDepth
