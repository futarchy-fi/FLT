/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.OpenNormalFixedField
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# The finite field cut out by a continuous finite representation

The field is the fixed field of the actual kernel, without a surjectivity
assumption. Its degree is the cardinality of the image, and inflation of its
faithful finite representation recovers the given homomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.Extensions

variable {K H : Type*} [Field K] [PerfectField K] [Group H]
  [TopologicalSpace H] [DiscreteTopology H]
  (f : Field.absoluteGaloisGroup K →ₜ* H)

local instance : IsGalois K (AlgebraicClosure K) where

/-- The open normal kernel of a finite discrete representation. -/
def finiteImageKernel : OpenNormalSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := f.toMonoidHom.ker
  isOpen' := (isOpen_discrete ({1} : Set H)).preimage f.continuous
  isNormal' := inferInstance

/-- The finite Galois field fixed by the actual kernel. -/
def finiteImageField : FiniteGaloisIntermediateField K (AlgebraicClosure K) :=
  openNormalFixedField (finiteImageKernel f)

/-- The field cuts out exactly the representation kernel. -/
theorem finiteImageField_fixingSubgroup :
    (finiteImageField f).toIntermediateField.fixingSubgroup = f.toMonoidHom.ker :=
  fixingSubgroup_openNormal (finiteImageKernel f)

/-- Its Galois group identifies with the image, not the possibly larger target. -/
def finiteImageFieldEquiv : Gal(finiteImageField f/K) ≃* f.toMonoidHom.range := by
  letI : (finiteImageKernel f).toSubgroup.Normal := (finiteImageKernel f).isNormal'
  exact (openNormalQuotientEquiv (finiteImageKernel f)).symm.trans
    (QuotientGroup.quotientKerEquivRange f.toMonoidHom)

/-- The faithful representation on this finite Galois group. -/
def finiteImageRepresentation : Gal(finiteImageField f/K) →* H :=
  f.toMonoidHom.range.subtype.comp (finiteImageFieldEquiv f).toMonoidHom

/-- Restriction followed by the finite representation is the original map. -/
theorem finiteImageRepresentation_restrict (g : Field.absoluteGaloisGroup K) :
    finiteImageRepresentation f (AlgEquiv.restrictNormalHom (finiteImageField f) g) = f g := by
  change ((QuotientGroup.quotientKerEquivRange f.toMonoidHom)
    ((openNormalQuotientEquiv (finiteImageKernel f)).symm
      (AlgEquiv.restrictNormalHom (openNormalFixedField (finiteImageKernel f)) g))).val = f g
  erw [← openNormalQuotientEquiv_mk (finiteImageKernel f), MulEquiv.symm_apply_apply]
  rfl

/-- Faithfulness records that the field has no unnecessary extension. -/
theorem finiteImageRepresentation_injective : Function.Injective (finiteImageRepresentation f) :=
  Subtype.val_injective.comp (finiteImageFieldEquiv f).injective

/-- The extension degree is exactly the size of the image. -/
theorem finiteImageField_finrank :
    Module.finrank K (finiteImageField f) = Nat.card f.toMonoidHom.range := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (finiteImageFieldEquiv f).toEquiv

/-- A uniform target supplies a uniform degree bound. -/
theorem finiteImageField_finrank_le [Finite H] :
    Module.finrank K (finiteImageField f) ≤ Nat.card H := by
  rw [finiteImageField_finrank]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end GaloisRepresentation.Extensions
