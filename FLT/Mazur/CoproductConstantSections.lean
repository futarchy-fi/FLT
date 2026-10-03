/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCoproductSections
public import FLT.Mazur.ProjectiveLineConstantSections
/-!
# Constants on coproducts of schemes over a field

When each component has only constant global functions, the global functions
of the specified coproduct are its coordinate values, linearly over the base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.CoproductConstantSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve SchemeCoproductSections
variable {K : Type u} [Field K] {ι : Type}
  (X : ι → Over (Spec (.of K))) (h : ∀ i, HasConstantGlobalSections (X i).hom)
/-- Constant sections on each component give the ring of coordinate values. -/
def ringEquiv : Γ((∐ X).left, ⊤) ≃+* (ι → K) :=
  (overIso X).commRingCatIsoToRingEquiv.trans
    (RingEquiv.piCongrRight fun i ↦
      (RingEquiv.ofBijective (structureScalarMap (X i).hom) (h i)).symm)
theorem coordinate (r : Γ((∐ X).left, ⊤)) (i : ι) :
    structureScalarMap (X i).hom (ringEquiv X h r i) = (Sigma.ι X i).left.appTop r := by
  change (RingEquiv.ofBijective (structureScalarMap (X i).hom) (h i))
    ((RingEquiv.ofBijective (structureScalarMap (X i).hom) (h i)).symm
      ((overIso X).hom r i)) = _
  rw [RingEquiv.apply_symm_apply, overIso_apply]
theorem scalar (a : K) (i : ι) :
    ringEquiv X h (structureScalarMap (∐ X).hom a) i = a := by
  apply (h i).injective
  rw [coordinate]
  have he := congrArg (fun f ↦ structureScalarMap f a) (Sigma.ι X i).w
  simpa only [structureScalarMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.hom_comp, RingHom.comp_apply] using he

/-- Componentwise constants respect the specified base-field action. -/
def linearEquiv :
    letI := Module.compHom Γ((∐ X).left, ⊤) (structureScalarMap (∐ X).hom)
    Γ((∐ X).left, ⊤) ≃ₗ[K] (ι → K) := by
  letI := Module.compHom Γ((∐ X).left, ⊤) (structureScalarMap (∐ X).hom)
  refine { toAddEquiv := (ringEquiv X h).toAddEquiv, map_smul' := ?_ }
  intro a r
  change ringEquiv X h (structureScalarMap (∐ X).hom a * r) = _
  rw [map_mul]
  ext i
  exact congrArg (fun b ↦ b * ringEquiv X h r i) (scalar X h a i)
end FLT.Mazur.CoproductConstantSections
