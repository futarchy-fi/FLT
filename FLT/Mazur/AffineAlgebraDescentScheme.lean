/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentReconstruction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Constructed affine schemes from multiplicative descent data

The spectrum of the fixed coordinate algebra is a constructed affine scheme.
Its base change is the original coefficient scheme, with both projections
specified. Faithful flatness makes the comparison a covering morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : Data R S B)

/-- The affine scheme constructed from the fixed ring of the original datum. -/
def descendedScheme : Scheme := Spec (.of (invariants D))

/-- The original coefficients map to the constructed affine scheme. -/
def schemeProjection : Spec (.of B) ⟶ descendedScheme D :=
  Spec.map (CommRingCat.ofHom (invariants D).val.toRingHom)

/-- The constructed scheme lies over the original base. -/
def schemeBase : descendedScheme D ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (invariants D)))

section Flat
variable [Module.Flat R S]

/-- Effective reconstruction gives the actual affine base-change square. -/
theorem scheme_isPullback : IsPullback (schemeProjection D)
    (Spec.map (CommRingCat.ofHom (algebraMap S B))) (schemeBase D)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply IsPullback.flip
  apply isPullback_SpecMap_of_isPushout
  apply (CommRingCat.isPushout_tensorProduct R S (invariants D)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (reconstruction D).toRingEquiv.toCommRingCatIso (by simp) (by simp)
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change reconstruct D (s ⊗ₜ[R] (1 : invariants D)) = algebraMap S B s
    rw [reconstruct_tmul]
    exact Algebra.smul_def s (1 : B) |>.trans (mul_one _)
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change reconstruct D ((1 : S) ⊗ₜ[R] b) = b.val
    rw [reconstruct_tmul, one_smul]

/-- The constructed scheme reconstructs the original affine scheme under base change. -/
def schemeReconstruction : Spec (.of B) ≅
    pullback (schemeBase D) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (scheme_isPullback D).isoPullback

/-- Reconstruction preserves the projection to the constructed quotient scheme. -/
@[reassoc]
theorem schemeReconstruction_fst :
    (schemeReconstruction D).hom ≫ pullback.fst _ _ = schemeProjection D :=
  (scheme_isPullback D).isoPullback_hom_fst

/-- Reconstruction preserves the original covering-base coordinate. -/
@[reassoc]
theorem schemeReconstruction_snd : (schemeReconstruction D).hom ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S B)) :=
  (scheme_isPullback D).isoPullback_hom_snd

instance schemeProjection_flat : Flat (schemeProjection D) := by
  have h : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact MorphismProperty.of_isPullback (scheme_isPullback D).flip h

end Flat

instance schemeProjection_surjective [Module.FaithfullyFlat R S] :
    Surjective (schemeProjection D) := by
  have h := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact MorphismProperty.of_isPullback (scheme_isPullback D).flip h.2

end FLT.Mazur.AffineAlgebraDescent
