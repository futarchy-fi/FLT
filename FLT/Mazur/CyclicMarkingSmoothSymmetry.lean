/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSmoothCarrier
public import FLT.Mazur.GeneralizedCurveGeneratorTransport

/-!
# Unit and inverse preserve cyclic divisors in singular families

The cyclic group of labels supplies the identity and permutes inverse factors.
These are identities of full ideals on the smooth group, retaining repeated
labels; the whole curve need not carry a group law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Residue indexing retains each group-section factor with its multiplicity. -/
theorem cyclicMarkingGroupIdeal_zmod : E.cyclicMarkingGroupIdeal φ =
    ∏ i : ZMod n, (φ (.ofAdd i)).left.ker := by
  rw [cyclicMarkingGroupIdeal_eq_prod, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have hv : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [← hv, ZMod.natCast_zmod_val]

/-- Each original group section factors through the entire orbit product. -/
theorem cyclicMarkingGroupIdeal_le_section (i : ZMod n) :
    E.cyclicMarkingGroupIdeal φ ≤ (φ (.ofAdd i)).left.ker := by
  classical
  rw [cyclicMarkingGroupIdeal_zmod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  intro U
  exact Ideal.mul_le_left

/-- The identity label proves the unit equation on the actual group divisor. -/
theorem cyclicMarkingGroupIdeal_unitEquation :
    ClosedGroupIdeal.unitEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 := by
  apply (FCurve.idealModulePullbackι_eq_zero_iff _ _).mpr
  have h := E.cyclicMarkingGroupIdeal_le_section φ 0
  change E.cyclicMarkingGroupIdeal φ ≤ (φ 1).left.ker at h
  simpa only [map_one, MonObj.one_eq_one] using h

/-- Inversion preserves the exact product ideal, including coincident labels. -/
theorem cyclicMarkingGroupIdeal_inverse :
    (E.cyclicMarkingGroupIdeal φ).comap (ι[E.group]).left = E.cyclicMarkingGroupIdeal φ := by
  have : IsProper E.curve.hom := E.family.family.1
  have : IsSeparated E.group.hom := by
    rw [← E.inclusion.w]
    infer_instance
  rw [cyclicMarkingGroupIdeal_zmod, FCurve.idealSheaf_comap_prod]
  calc
    _ = ∏ i : ZMod n, (φ (.ofAdd (-i))).left.ker := by
      apply Finset.prod_congr rfl
      intro i _
      have : IsClosedImmersion (φ (.ofAdd i)).left :=
        FCurve.isClosedImmersion_section E.group.hom _ (Over.w _)
      let e : E.group.left ≅ E.group.left :=
        (Over.forget S).mapIso (asIso ι[E.group])
      have h := FiniteSubgroup.ker_comp_iso (φ (.ofAdd i)).left e
      change _ = (φ (.ofAdd i)).left.ker.comap (inv ι[E.group]).left at h
      rw [GrpObj.inv_inv] at h
      rw [← h]
      have hi : φ (.ofAdd i) ≫ ι[E.group] = φ (.ofAdd (-i)) := by
        change (φ (.ofAdd i))⁻¹ = _
        rw [← map_inv]
        rfl
      exact congrArg (fun f ↦ f.left.ker) hi
    _ = _ := Equiv.prod_comp (Equiv.neg (ZMod n)) (fun i ↦ (φ (.ofAdd i)).left.ker)

/-- Inversion factors through the full orbit divisor without multiplication hypotheses. -/
theorem cyclicMarkingGroupIdeal_inverseEquation :
    ClosedGroupIdeal.inverseEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 := by
  apply (FCurve.idealModulePullbackι_eq_zero_iff_comap _ _).mpr
  change (E.cyclicMarkingGroupIdeal φ).comap
    ((E.cyclicMarkingGroupIdeal φ).subschemeι ≫ (ι[E.group]).left) = ⊥
  rw [Scheme.IdealSheafData.comap_comp, cyclicMarkingGroupIdeal_inverse]
  apply (FCurve.idealModulePullbackι_eq_zero_iff_comap _ _).mp
  apply (FCurve.idealModulePullbackι_eq_zero_iff _ _).mpr
  simp

end FLT.Mazur.GeneralizedEllipticCurve
