/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCyclotomicCover

/-!
# Affine coordinates on the actual integral cyclotomic cover

Over any ring the arithmetic cover is the spectrum of the scalar tensor
product with the integral cyclotomic ring. The comparison retains both maps,
so the original cyclotomic coordinate gives a specified unit on that cover.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.IntegralCyclotomicAffineCover

open IntegralCyclotomicCoordinates

variable (R : Type) [CommRing R] (n : ℕ)

/-- The actual affine scalar extension of the integral cyclotomic coordinate ring. -/
abbrev Algebra := R ⊗[ℤ] Coordinate n

/-- The specified arithmetic structural map to the integer spectrum. -/
abbrev arithmeticMap : Spec (.of R) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ R))

/-- The spectrum of the scalar tensor algebra is the actual cyclotomic cover. -/
def schemeIso : Spec (.of (Algebra R n)) ≅ (IntegralCyclotomicCover.cover n
    (arithmeticMap R)).left :=
  (pullbackSpecIso ℤ R (Coordinate n)).symm ≪≫ pullbackSymmetry _ _

/-- The comparison retains the structural morphism of the cover over the test ring. -/
@[reassoc] theorem schemeIso_base :
    (schemeIso R n).hom ≫ (IntegralCyclotomicCover.cover n (arithmeticMap R)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n))) := by
  change (pullbackSpecIso ℤ R (Coordinate n)).inv ≫
    (pullbackSymmetry _ _).hom ≫ pullback.snd _ _ = _
  rw [pullbackSymmetry_hom_comp_snd]
  exact pullbackSpecIso_inv_fst' ℤ R (Coordinate n)

/-- The original integral root specializes along the right tensor factor. -/
def specialization : Coordinate n →+* Algebra R n :=
  (Algebra.TensorProduct.includeRight : Coordinate n →ₐ[ℤ] Algebra R n).toRingHom

/-- The cover projection retains the specified specialization of the cyclotomic ring. -/
@[reassoc] theorem schemeIso_cyclotomic :
    (schemeIso R n).hom ≫ pullback.fst (IntegralCyclotomicCover.model n).hom
      (arithmeticMap R) = Spec.map (CommRingCat.ofHom (specialization R n)) := by
  change (pullbackSpecIso ℤ R (Coordinate n)).inv ≫
    (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_hom_comp_fst]
  exact pullbackSpecIso_inv_snd ℤ R (Coordinate n)

/-- The coordinate comparison also retains the base as an isomorphism of over-schemes. -/
def overIso : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n)))) ≅
    IntegralCyclotomicCover.cover n (arithmeticMap R) :=
  Over.isoMk (schemeIso R n) (schemeIso_base R n)

/-- The cyclotomic tensor spectrum is finite locally free of the same explicit degree. -/
theorem degree : FCurve.FiniteLocallyFreeDegree
    (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n)))) n.totient := by
  exact (FCurve.finiteLocallyFreeDegree_iff_of_overIso (overIso R n)).mpr
    (IntegralCyclotomicCover.cover_degree n (arithmeticMap R))

/-- The explicit affine arithmetic cover is fppf without inverting the root order. -/
theorem fppf [NeZero n] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n)))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n)))) ∧
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra R n)))) :=
  ⟨(degree R n).2.1, (degree R n).surjective (rank_pos n), (degree R n).2.2.1⟩

end FLT.Mazur.IntegralCyclotomicAffineCover
