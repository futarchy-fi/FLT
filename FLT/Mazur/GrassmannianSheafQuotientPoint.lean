/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientSheafFaithful

/-!
# Original relations of an affine sheaf quotient

A sheaf epimorphism with a finite projective affine presentation determines its
entire algebraic kernel. The resulting Grassmannian quotient recovers the given
sheaf and its original ambient projection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable {P : (Spec (.of A)).Modules}
  (p : tilde (ModuleCat.of A (A ⊗[R] M)) ⟶ P) [Epi p]
variable (Q : ModuleCat.{u} A) [Module.Finite A Q] [Module.Projective A Q]
  (e : tilde Q ≅ P) (hd : ∀ x : PrimeSpectrum A, Module.rankAtStalk (R := A) Q x = d)

/-- Full faithfulness recovers the original affine quotient map in chosen target coordinates. -/
def sheafQuotientLinearMap : (A ⊗[R] M) →ₗ[A] Q :=
  ((tilde.fullyFaithfulFunctor (R := .of A)).preimage (p ≫ e.inv)).hom

omit [Epi p] [Module.Finite A Q] [Module.Projective A Q] in
/-- The recovered linear map sheafifies to the entire given ambient projection. -/
@[reassoc] theorem sheafQuotientLinearMap_tilde :
    (tilde.functor (.of A)).map (ModuleCat.ofHom (sheafQuotientLinearMap p Q e)) ≫
      e.hom = p := by
  change (tilde.functor (.of A)).map
    ((tilde.fullyFaithfulFunctor (R := .of A)).preimage (p ≫ e.inv)) ≫ e.hom = p
  rw [(tilde.fullyFaithfulFunctor (R := .of A)).map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [Module.Finite A Q] [Module.Projective A Q] in
/-- The sheaf epimorphism yields an actual surjection of the affine modules. -/
theorem sheafQuotientLinearMap_surjective : Function.Surjective (sheafQuotientLinearMap p Q e) := by
  apply (ModuleCat.epi_iff_surjective (ModuleCat.ofHom (sheafQuotientLinearMap p Q e))).mp
  let _ := (tilde.fullyFaithfulFunctor (R := .of A)).faithful
  apply Functor.epi_of_epi_map (tilde.functor (.of A))
  have he : (tilde.functor (.of A)).map
      (ModuleCat.ofHom (sheafQuotientLinearMap p Q e)) = p ≫ e.inv :=
    (tilde.fullyFaithfulFunctor (R := .of A)).map_preimage _
  rw [he]
  infer_instance

/-- The quotient by all recovered relations is the original affine target module. -/
def sheafQuotientKernelEquiv :
    ((A ⊗[R] M) ⧸ (sheafQuotientLinearMap p Q e).ker) ≃ₗ[A] Q :=
  (sheafQuotientLinearMap p Q e).quotKerEquivOfSurjective
    (sheafQuotientLinearMap_surjective p Q e)

/-- The entire original affine kernel defines the required fixed-rank Grassmannian point. -/
def sheafQuotientPoint : Module.Grassmannian A (A ⊗[R] M) d where
  toSubmodule := (sheafQuotientLinearMap p Q e).ker
  finite_quotient := Module.Finite.equiv (sheafQuotientKernelEquiv p Q e).symm
  projective_quotient := Module.Projective.of_equiv (sheafQuotientKernelEquiv p Q e).symm
  rankAtStalk_eq x :=
    (congrFun (Module.rankAtStalk_eq_of_equiv (sheafQuotientKernelEquiv p Q e)) x).trans
      (hd x)

/-- The constructed point retains exactly the kernel of the original affine projection. -/
theorem sheafQuotientPoint_relation :
    (sheafQuotientPoint p Q e hd).toSubmodule = (sheafQuotientLinearMap p Q e).ker := rfl

/-- The original sheaf target is recovered by a constructed isomorphism. -/
def sheafQuotientPointIso : grassmannianQuotientSheaf (sheafQuotientPoint p Q e hd) ≅ P :=
  (tilde.functor (.of A)).mapIso (sheafQuotientKernelEquiv p Q e).toModuleIso ≪≫ e

/-- Recovery preserves the full original ambient quotient, including every relation. -/
@[reassoc] theorem sheafQuotientPointIso_projection :
    grassmannianQuotientSheafMap (sheafQuotientPoint p Q e hd) ≫
      (sheafQuotientPointIso p Q e hd).hom = p := by
  have h : ModuleCat.ofHom (sheafQuotientPoint p Q e hd).toSubmodule.mkQ ≫
      (sheafQuotientKernelEquiv p Q e).toModuleIso.hom =
        ModuleCat.ofHom (sheafQuotientLinearMap p Q e) := by
    ext x
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _
      (sheafQuotientLinearMap_surjective p Q e) x
  dsimp only [sheafQuotientPointIso, Iso.trans_hom, Functor.mapIso_hom,
    grassmannianQuotientSheafMap]
  rw [← Category.assoc, ← Functor.map_comp, h, sheafQuotientLinearMap_tilde]

end FLT.Mazur.GrassmannianChart
