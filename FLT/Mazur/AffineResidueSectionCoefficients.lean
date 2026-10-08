/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Residue-spectrum sections in ideal-residue-field coordinates

The canonical affine and residue-field comparisons carry the actual structural
action on residue-spectrum functions to the usual ideal-residue-field action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation

variable (R : CommRingCat.{0})

/-- Canonical coordinates for the global functions of an affine spectrum. -/
abbrev affineSectionRingEquiv : Γ(Spec R, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

local instance : RingHomInvPair (affineSectionRingEquiv R).toRingHom
    (affineSectionRingEquiv R).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (affineSectionRingEquiv R)

local instance : RingHomInvPair (affineSectionRingEquiv R).symm.toRingHom
    (affineSectionRingEquiv R).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (affineSectionRingEquiv R)

variable (b : Spec R)

/-- Actual functions on the residue spectrum identify with the ideal residue field. -/
def residueSectionRingEquiv :
    Γ(Spec ((Spec R).residueField b), ⊤) ≃+* b.asIdeal.ResidueField :=
  (affineSectionRingEquiv ((Spec R).residueField b)).trans
    (Scheme.Spec.residueFieldIso R b).commRingCatIsoToRingEquiv

/-- The actual residue morphism has the usual residue scalar map in affine coordinates. -/
lemma residueSectionRingEquiv_scalar (r : Γ(Spec R, ⊤)) :
    residueSectionRingEquiv R b (((Spec R).fromSpecResidueField b).appTop r) =
      algebraMap R b.asIdeal.ResidueField (affineSectionRingEquiv R r) := by
  change (((Spec R).fromSpecResidueField b).appTop ≫
    (Scheme.ΓSpecIso _).hom ≫ (Scheme.Spec.residueFieldIso R b).hom) r = _
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Scheme.ΓSpecIso_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Residue-spectrum coefficients are semilinearly the ordinary ideal residue field. -/
def residueSectionSemilinearEquiv :
    let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
      ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
    Γ(Spec ((Spec R).residueField b), ⊤) ≃ₛₗ[(affineSectionRingEquiv R).toRingHom]
      b.asIdeal.ResidueField :=
  let _ : Algebra Γ(Spec R, ⊤) Γ(Spec ((Spec R).residueField b), ⊤) :=
    ((Spec R).fromSpecResidueField b).appTop.hom.toAlgebra
  { (residueSectionRingEquiv R b).toAddEquiv with
    map_smul' := fun r x ↦ by
      change residueSectionRingEquiv R b
        ((((Spec R).fromSpecResidueField b).appTop r) * x) = _
      rw [map_mul, residueSectionRingEquiv_scalar, Algebra.smul_def]
      rfl }

end FLT.Mazur.Approximation
