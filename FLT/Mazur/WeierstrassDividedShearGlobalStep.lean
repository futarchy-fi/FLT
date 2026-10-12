/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearGlobalIso
public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep

/-!
# Compatibility of the global shear with every original finite step

The translated infinity lift and complete local comparison both respect
successive contractions, hence so does the entire global isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "dat" => fun a => shearData (data a) r
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl
local notation "E" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "F" => initialExterior (shearData (data (Fin.mk 0 (Nat.zero_lt_succ n))) r)
local notation "m₁" => shearFiniteModificationIso hπ data r (j + 1) hj
local notation "m₀" => shearFiniteModificationIso hπ data r j (Nat.le_of_succ_le hj)
local notation "e₁" => shearFiniteGlobalIso hπ data r (j + 1) hj
local notation "e₀" => shearFiniteGlobalIso hπ data r j (Nat.le_of_succ_le hj)

omit [IsBezout R] in
/-- The actual local finite shear retains every preceding contraction. -/
@[reassoc] theorem shearFiniteModificationIso_step :
    (m₁).hom ≫ finiteStep hπ data E j hj = finiteStep hπ dat F j hj ≫ (m₀).hom :=
  finiteWholeShearIso_step hπ data r E F _ _ j hj

omit [IsBezout R] in
/-- The inverse local finite comparison also retains the original preceding contraction. -/
@[reassoc] theorem shearFiniteModificationIso_inv_step :
    (m₁).inv ≫ finiteStep hπ dat F j hj = finiteStep hπ data E j hj ≫ (m₀).inv := by
  apply (cancel_epi (m₁).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, shearFiniteModificationIso_step,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every translated infinity lift retains the full original global step. -/
@[reassoc] theorem shearFiniteInfinityLift_step :
    shearFiniteInfinityLift hπ data r (j + 1) hj ≫ finiteGlobalStep hπ dat j hj =
      shearFiniteInfinityLift hπ data r j (Nat.le_of_succ_le hj) := by
  apply SchemeUnchangedOpen.lift_unique
  rw [Category.assoc, ← Category.assoc (finiteGlobalStep hπ dat j hj),
    finiteGlobalStep_contraction, shearFiniteInfinityLift_contraction]

/-- The full inverse global comparison commutes with every original finite step. -/
@[reassoc] theorem shearFiniteGlobalIso_inv_step :
    (e₁).inv ≫ finiteGlobalStep hπ dat j hj = finiteGlobalStep hπ data j hj ≫ (e₀).inv := by
  apply pushout.hom_ext
  · change finiteInfinityChart hπ data (j + 1) hj ≫ _ =
      finiteInfinityChart hπ data (j + 1) hj ≫ _
    rw [shearFiniteGlobalIso_inv_infinity_assoc, shearFiniteInfinityLift_step,
      finiteGlobalStep_infinity_assoc, shearFiniteGlobalIso_inv_infinity]
  · change finiteLocalChart hπ data (j + 1) hj ≫ _ =
      finiteLocalChart hπ data (j + 1) hj ≫ _
    rw [shearFiniteGlobalIso_inv_local_assoc, finiteGlobalStep_local,
      ← Category.assoc, shearFiniteModificationIso_inv_step, Category.assoc,
      finiteGlobalStep_local_assoc, shearFiniteGlobalIso_inv_local]

/-- The actual original finite global tower is identified with its integral shear. -/
@[reassoc] theorem shearFiniteGlobalIso_step :
    (e₁).hom ≫ finiteGlobalStep hπ data j hj = finiteGlobalStep hπ dat j hj ≫ (e₀).hom := by
  apply (cancel_epi (e₁).inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, shearFiniteGlobalIso_inv_step,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
