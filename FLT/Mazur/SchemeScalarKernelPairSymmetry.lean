/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarAvoidanceCover
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original scalar invariance on the full kernel pair

The two kernel-pair endpoints agree on every original scalar as full sections.
Consequently the endpoint transposition fixes these scalars exactly. No residue
fields, reduced fibers, or finiteness of the scalar ring are needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} (σ : R →+* Γ(X, ⊤))

/-- The geometric scalar morphism recovers the unchanged scalar ring homomorphism. -/
theorem scalarMorphism_app_original (a : R) :
    (scalarMorphism σ).appTop ((Scheme.ΓSpecIso (.of R)).inv a) = σ a := by
  have h : (Scheme.ΓSpecIso (.of R)).inv ≫ (scalarMorphism σ).appTop =
      CommRingCat.ofHom σ := by
    unfold scalarMorphism
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun f : CommRingCat.of R ⟶ Γ(X, ⊤) ↦ f a) h

local notation "f" => scalarMorphism σ

/-- The full two endpoint sections agree on every original scalar. -/
theorem scalarKernelPair_endpoints (a : R) :
    (pullback.fst f f).appTop (σ a) = (pullback.snd f f).appTop (σ a) := by
  have h := congrArg (fun g : pullback f f ⟶ Spec (.of R) ↦
    g.appTop ((Scheme.ΓSpecIso (.of R)).inv a))
      (show pullback.fst f f ≫ f = pullback.snd f f ≫ f from pullback.condition)
  change (pullback.fst f f).appTop ((f).appTop _) =
    (pullback.snd f f).appTop ((f).appTop _) at h
  simpa only [scalarMorphism_app_original σ a] using h

/-- Endpoint transposition fixes the complete original scalar map, not just its image support. -/
theorem scalarKernelPair_transpose_scalars :
    (pullbackSymmetry f f).hom.appTop.hom.comp ((pullback.fst f f).appTop.hom.comp σ) =
      (pullback.fst f f).appTop.hom.comp σ := by
  ext a
  change ((pullbackSymmetry f f).hom ≫ pullback.fst f f).appTop (σ a) = _
  rw [pullbackSymmetry_hom_comp_fst]
  exact (scalarKernelPair_endpoints σ a).symm

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
