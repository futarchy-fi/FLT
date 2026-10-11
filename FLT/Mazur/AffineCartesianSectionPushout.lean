/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Cartesian affine sections with the original coefficients

The section pushout of an affine cartesian square is transported through
the canonical spectrum-section isomorphisms on the two coefficient rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineCartesianSectionPushout

set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

/-- The structural map from the original coefficients to global sections. -/
def scalars (f : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- Cartesian affine schemes yield a pushout over the original coefficient rings. -/
theorem isPushout [IsAffine X]
    (i : Y ⟶ X) (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of S)) (r : R →+* S)
    (h : IsPullback i g f (Spec.map (CommRingCat.ofHom r))) :
    IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (scalars f))
      (CommRingCat.ofHom (scalars g)) i.appTop := by
  apply (isPushout_appTop_of_isPullback h).flip.of_iso'
    (Scheme.ΓSpecIso (.of R)).symm (Scheme.ΓSpecIso (.of S)).symm
    (Iso.refl _) (Iso.refl _)
  · exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r)).symm
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl
  · simp

/-- On an affine scheme the structural coefficient map recovers the original morphism. -/
theorem fromSpec_toBase [IsAffine X] (f : X ⟶ Spec (.of R)) :
    X.isoSpec.inv ≫ f = Spec.map (CommRingCat.ofHom (scalars f)) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- When the total chart is a spectrum, its original coordinate ring is retained as well. -/
theorem isPushout_spec {A : Type u} [CommRing A]
    (i : Y ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of S)) (a : R →+* A) (r : R →+* S)
    (h : IsPullback i g (Spec.map (CommRingCat.ofHom a))
      (Spec.map (CommRingCat.ofHom r))) :
    IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom a)
      (CommRingCat.ofHom (scalars g)) (CommRingCat.ofHom (scalars i)) := by
  apply (isPushout i _ g r h).of_iso' (Iso.refl _) (Iso.refl _)
    (Scheme.ΓSpecIso (.of A)).symm (Iso.refl _)
  · simp
  · apply CommRingCat.hom_ext
    exact congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom a)).symm
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl

end FLT.Mazur.AffineCartesianSectionPushout
