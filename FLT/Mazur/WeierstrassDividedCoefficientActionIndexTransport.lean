/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterStructure
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverAction

/-!
# The actual coefficient point action commutes with stage-index transport

Changing the written natural-number expression for a finite stage preserves
both the coefficient structure and the original action on every test scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
local notation "transport" =>
  eqToHom (finiteGlobalTensorModel_index_congr hπ data S ha hb he)
local notation "fstA" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (finiteGlobalStructure hπ data a ha)
local notation "fstB" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (finiteGlobalStructure hπ data b hb)

/-- The original coefficient action is unchanged by reassociating its stage index. -/
theorem finiteGlobalCoefficientPointAction_index_transport {T : Scheme.{u}}
    (x : T ⟶ (integralSmoothOpen (W.map (algebraMap R S))).toScheme)
    (y : T ⟶ finiteGlobalTensorModel hπ data S a ha)
    (hxy : x ≫ integralSmoothStructure (W.map (algebraMap R S)) = y ≫ fstA) :
    finiteGlobalCoefficientPointAction hπ data b hb S x (y ≫ transport)
        (by
          rw [Category.assoc, finiteGlobalTensorModel_structure_transport hπ data S ha hb he]
          exact hxy) =
      finiteGlobalCoefficientPointAction hπ data a ha S x y hxy ≫ transport := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
