/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalFunctionsPushout
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Flat global functions over the unchanged scalar ring

The affine-base section pushout is transported back to the original rings,
including a non-Noetherian invariant ring. Its maps retain the literal
geometric projection and scalar inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FlatScalarFunctionPushout
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X P : Scheme.{0}} [Algebra R Γ(X, ⊤)]
  {a : P ⟶ X} {b : P ⟶ Spec (.of S)}
  (h : IsPullback a b (scalarMorphism (algebraMap R Γ(X, ⊤)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- The actual scalar map on functions of a scheme over an affine scalar base. -/
def scalarMap (b : P ⟶ Spec (.of S)) : S →+* Γ(P, ⊤) :=
  ((Scheme.ΓSpecIso (.of S)).inv ≫ b.appTop).hom

/-- Passing through the spectrum of a ring does not change the original scalar map. -/
theorem scalarMap_scalarMorphism :
    scalarMap (scalarMorphism (algebraMap R Γ(X, ⊤))) = algebraMap R Γ(X, ⊤) := by
  unfold scalarMap scalarMorphism
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

variable [CompactSpace X] [QuasiSeparatedSpace X] [Module.Flat R S]

include h in
/-- Flat geometric base change is a pushout over the original scalar ring itself. -/
theorem scalar_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap R S)) a.appTop (CommRingCat.ofHom (scalarMap b)) := by
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply (Approximation.isPushout_appTop_of_flat_cartesian h).of_iso
    (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of S)) (Iso.refl _)
  · rw [Iso.refl_hom, Category.comp_id,
      ← cancel_epi (Scheme.ΓSpecIso (.of R)).inv, Iso.inv_hom_id_assoc]
    exact congrArg CommRingCat.ofHom (scalarMap_scalarMorphism (R := R) (X := X))
  · exact Scheme.ΓSpecIso_naturality _
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, scalarMap, CommRingCat.ofHom_hom, Iso.hom_inv_id_assoc,
      Category.comp_id]

/-- All functions on the full pullback are the scalar tensor product of original functions. -/
def sectionsEquiv : S ⊗[R] Γ(X, ⊤) ≃+* Γ(P, ⊤) :=
  ((CommRingCat.isPushout_tensorProduct R S Γ(X, ⊤)).isoIsPushout _ _
    (scalar_isPushout h).flip).commRingCatIsoToRingEquiv

/-- The left tensor inclusion is the original geometric scalar map. -/
theorem sectionsEquiv_left (s : S) :
    sectionsEquiv h (algebraMap S (S ⊗[R] Γ(X, ⊤)) s) = scalarMap b s :=
  congrArg (fun f ↦ f.hom s)
    ((CommRingCat.isPushout_tensorProduct R S Γ(X, ⊤)).inl_isoIsPushout_hom _ _
      (scalar_isPushout h).flip)

/-- The right tensor inclusion is pullback of the literal original function. -/
theorem sectionsEquiv_right (x : Γ(X, ⊤)) :
    sectionsEquiv h (1 ⊗ₜ[R] x) = a.appTop x :=
  congrArg (fun f ↦ f.hom x)
    ((CommRingCat.isPushout_tensorProduct R S Γ(X, ⊤)).inr_isoIsPushout_hom _ _
      (scalar_isPushout h).flip)

/-- Every pure tensor uses the two full geometric projection maps. -/
theorem sectionsEquiv_tmul (s : S) (x : Γ(X, ⊤)) :
    sectionsEquiv h (s ⊗ₜ[R] x) = scalarMap b s * a.appTop x := by
  rw [← sectionsEquiv_left h, ← sectionsEquiv_right h, ← map_mul]
  simp only [Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply]

end FLT.Mazur.FlatScalarFunctionPushout
