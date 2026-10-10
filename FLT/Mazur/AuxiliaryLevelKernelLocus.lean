/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelRelabeling

/-!
# Closed loci where a marked element vanishes

The bad locus uses scheme equalizers, so equality includes residue-field data.
Relabeling transports each actual equalizer isomorphically. These closed loci
will be removed to construct the open scheme of fiberwise faithful markings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] {A : Type} [Group A] [Fintype A]

/-- The scheme where the selected universal marked section is the identity. -/
def kernelScheme (a : A) : Over S := equalizer (value E A a) 1

/-- Its actual equalizer inclusion. -/
def kernelInclusion (a : A) : kernelScheme E a ⟶ homScheme E A := equalizer.ι _ _

/-- The marked element is the identity on its kernel scheme. -/
@[reassoc] theorem kernelInclusion_value (a : A) :
    kernelInclusion E a ≫ value E A a = 1 := by
  rw [kernelInclusion, equalizer.condition, MonObj.comp_one]

/-- The kernel locus retains equality of scheme maps, not just topological images. -/
def kernelLocus (a : A) : Set (homScheme E A).left := Set.range (kernelInclusion E a).left

/-- Separatedness of the group makes each kernel equation closed. -/
theorem kernelLocus_isClosed [IsSeparated E.hom] (a : A) : IsClosed (kernelLocus E a) := by
  let _ : IsClosedImmersion (kernelInclusion E a).left :=
    isClosedImmersion_equalizer_ι_left (value E A a) 1
  exact (IsClosedImmersion.isClosedEmbedding (kernelInclusion E a).left).isClosed_range

/-- The inverse relabeling formula on sections. -/
@[reassoc] theorem relabelAut_inv_value (e : MulAut A) (a : A) :
    (relabelAut E e).inv ≫ value E A a = value E A (e a) :=
  relabel_value E _ _

/-- Relabeling restricts to an isomorphism of the actual kernel schemes. -/
def kernelRelabelIso (e : MulAut A) (a : A) :
    kernelScheme E (e.symm a) ≅ kernelScheme E a where
  hom := equalizer.lift
    (kernelInclusion E (e.symm a) ≫ (relabelAction E e).hom) (by
      rw [Category.assoc, relabelAction_value, kernelInclusion_value, MonObj.comp_one])
  inv := equalizer.lift (kernelInclusion E a ≫ (relabelAut E e).inv) (by
    rw [Category.assoc, relabelAut_inv_value, e.apply_symm_apply,
      kernelInclusion_value, MonObj.comp_one])
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      kernelInclusion, relabelAction, MonoidHom.coe_mk, OneHom.coe_mk,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      kernelInclusion, relabelAction, MonoidHom.coe_mk, OneHom.coe_mk,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The kernel comparison retains its inclusion in the original equation scheme. -/
@[reassoc] theorem kernelRelabelIso_hom_inclusion (e : MulAut A) (a : A) :
    (kernelRelabelIso E e a).hom ≫ kernelInclusion E a =
      kernelInclusion E (e.symm a) ≫ (relabelAction E e).hom := equalizer.lift_ι _ _

/-- The inverse comparison retains the ambient inverse action. -/
@[reassoc] theorem kernelRelabelIso_inv_inclusion (e : MulAut A) (a : A) :
    (kernelRelabelIso E e a).inv ≫ kernelInclusion E (e.symm a) =
      kernelInclusion E a ≫ (relabelAut E e).inv := equalizer.lift_ι _ _

/-- The ambient relabeling permutes the actual closed kernel loci. -/
theorem relabel_preimage_kernelLocus (e : MulAut A) (a : A) :
    (relabelSchemeAction E e).hom ⁻¹' kernelLocus E a = kernelLocus E (e.symm a) := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(kernelRelabelIso E e a).inv.left z, ?_⟩
    have h := congrArg (fun f => f.left z) (kernelRelabelIso_inv_inclusion E e a)
    change (kernelInclusion E (e.symm a)).left ((kernelRelabelIso E e a).inv.left z) =
      (relabelAut E e).inv.left ((kernelInclusion E a).left z) at h
    rw [hz] at h
    exact h.trans (congrArg (fun f : (homScheme E A).left ⟶ _ => f x)
      (relabelSchemeAction E e).hom_inv_id)
  · rintro ⟨z, rfl⟩
    refine ⟨(kernelRelabelIso E e a).hom.left z, ?_⟩
    exact congrArg (fun f => f.left z) (kernelRelabelIso_hom_inclusion E e a)

end FLT.Mazur.AuxiliaryLevel
