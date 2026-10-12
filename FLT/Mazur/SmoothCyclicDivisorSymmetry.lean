/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCyclicDivisorEquations
public import FLT.Mazur.GeneralizedCurveGeneratorTransport

/-!
# Unit and inverse preserve the entire cyclic orbit divisor

The identity is one of the ideal factors. Inversion permutes every cyclic
label, so it preserves the product with all multiplicities. Consequently
only the multiplication equation remains to define the subgroup locus.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Residue-class indexing lists exactly the original factors, with their multiplicities. -/
theorem cyclicMarkingIdeal_zmod : E.cyclicMarkingIdeal φ =
    ∏ i : ZMod n, (φ (.ofAdd i) ≫ E.inclusion).left.ker := by
  rw [cyclicMarkingIdeal, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have hv : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [← hv, ZMod.natCast_zmod_val]

/-- Every marked section factors through the multiplicity-preserving orbit divisor. -/
theorem cyclicMarkingIdeal_le_section (i : ZMod n) :
    E.cyclicMarkingIdeal φ ≤ (φ (.ofAdd i) ≫ E.inclusion).left.ker := by
  classical
  rw [cyclicMarkingIdeal_zmod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  intro U
  exact Ideal.mul_le_left

variable [Smooth E.curve.hom]
attribute [local instance] smoothCurveCommGrpObj

/-- The unit equation vanishes without assuming multiplication closure. -/
theorem cyclicDivisorUnitEquation_zero : E.cyclicDivisorUnitEquation φ = 0 := by
  apply (FCurve.idealModulePullbackι_eq_zero_iff _ _).mpr
  have h := E.cyclicMarkingIdeal_le_section φ 0
  have hu : φ (.ofAdd (0 : ZMod n)) ≫ E.inclusion = η[E.curve] := by
    change φ 1 ≫ E.inclusion = _
    rw [map_one]
    exact IsMonHom.one_hom E.inclusion
  rwa [hu] at h

omit [NeZero n] in
/-- Inversion carries each full-curve factor to the factor with opposite cyclic label. -/
theorem cyclicSection_inverse (i : ZMod n) :
    (φ (.ofAdd i) ≫ E.inclusion) ≫ ι[E.curve] = φ (.ofAdd (-i)) ≫ E.inclusion := by
  rw [Category.assoc, ← GrpObj.inv_hom]
  change (φ (.ofAdd i))⁻¹ ≫ E.inclusion = _
  rw [← map_inv]
  rfl

/-- The actual ideal is invariant under the full-curve inversion morphism. -/
theorem cyclicMarkingIdeal_inverse :
    (E.cyclicMarkingIdeal φ).comap (ι[E.curve]).left = E.cyclicMarkingIdeal φ := by
  have : IsProper E.curve.hom := E.family.family.1
  rw [cyclicMarkingIdeal_zmod, FCurve.idealSheaf_comap_prod]
  calc
    _ = ∏ i : ZMod n, (φ (.ofAdd (-i)) ≫ E.inclusion).left.ker := by
      apply Finset.prod_congr rfl
      intro i _
      have : IsClosedImmersion (φ (.ofAdd i) ≫ E.inclusion).left :=
        FCurve.isClosedImmersion_section E.curve.hom _ (Over.w _)
      let e : E.curve.left ≅ E.curve.left :=
        (Over.forget S).mapIso (asIso ι[E.curve])
      have h := FiniteSubgroup.ker_comp_iso (φ (.ofAdd i) ≫ E.inclusion).left e
      change _ = (φ (.ofAdd i) ≫ E.inclusion).left.ker.comap
        (inv ι[E.curve]).left at h
      rw [GrpObj.inv_inv] at h
      rw [← h]
      exact congrArg (fun f ↦ f.left.ker) (E.cyclicSection_inverse φ i)
    _ = _ := Equiv.prod_comp (Equiv.neg (ZMod n))
      (fun i ↦ (φ (.ofAdd i) ≫ E.inclusion).left.ker)

/-- The inverse equation vanishes without assuming multiplication closure. -/
theorem cyclicDivisorInverseEquation_zero : E.cyclicDivisorInverseEquation φ = 0 := by
  apply (FCurve.idealModulePullbackι_eq_zero_iff_comap _ _).mpr
  change (E.cyclicMarkingIdeal φ).comap
    ((E.cyclicMarkingIdeal φ).subschemeι ≫ (ι[E.curve]).left) = ⊥
  rw [Scheme.IdealSheafData.comap_comp, cyclicMarkingIdeal_inverse]
  apply (FCurve.idealModulePullbackι_eq_zero_iff_comap _ _).mp
  apply (FCurve.idealModulePullbackι_eq_zero_iff _ _).mpr
  simp

end FLT.Mazur.GeneralizedEllipticCurve
