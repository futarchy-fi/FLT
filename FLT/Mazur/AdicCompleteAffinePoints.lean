/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicAffineMorphismLift

/-!
# Affine points over the original complete ring

Compatible positive-order points reconstruct a point over the original complete
base, and the same restrictions detect equality of affine-valued points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AdicCompleteAffinePoints
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- Positive quotient coordinates detect elements of the original complete ring. -/
theorem element_ext {x y : R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (I ^ (m + 1)) x =
      Ideal.Quotient.mk (I ^ (m + 1)) y) : x = y := by
  apply (AdicCompletion.ofAlgEquiv I).injective
  apply (AdicCompletionPositiveLimit.equivalence I).injective
  apply Subtype.ext
  funext m
  change AdicCompletion.evalₐ I (m + 1) (AdicCompletion.of I R x) =
    AdicCompletion.evalₐ I (m + 1) (AdicCompletion.of I R y)
  simpa only [AdicCompletion.evalₐ_of] using h m

variable (Y : Scheme.{u}) [IsAffine Y]

/-- All positive adic restrictions detect maps to an affine scheme. -/
theorem hom_ext {f g : Spec (.of R) ⟶ Y}
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ g) : f = g := by
  apply (cancel_mono Y.isoSpec.hom).mp
  rw [← Spec.map_preimage (f ≫ Y.isoSpec.hom),
    ← Spec.map_preimage (g ≫ Y.isoSpec.hom)]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply element_ext I
  intro m
  have he := congrArg (fun k ↦ k ≫ Y.isoSpec.hom) (h m)
  simp only [Category.assoc] at he
  rw [← Spec.map_preimage (f ≫ Y.isoSpec.hom),
    ← Spec.map_preimage (g ≫ Y.isoSpec.hom)] at he
  rw [← Spec.map_comp, ← Spec.map_comp] at he
  have he' := Spec.map_injective he
  exact congrArg (fun k ↦ k.hom x) he'

variable (f : ∀ m : ℕ, Spec (.of (R ⧸ I ^ (m + 1))) ⟶ Y)
  (hf : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (S := I ^ (m + 2)) (T := I ^ (m + 1))
    (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ f (m + 1) = f m)

/-- Reconstruct on the original complete base, without replacing its coefficient ring. -/
def lift : Spec (.of R) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (AdicCompletion.ofAlgEquiv I).symm.toRingHom) ≫
    AdicAffineMorphismLift.lift I Y f hf

/-- Every positive-order restriction is the prescribed original scheme morphism. -/
@[reassoc] theorem quotient_lift (m : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫
      lift I Y f hf = f m := by
  rw [lift, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : (Ideal.Quotient.mk (I ^ (m + 1))).comp
      (AdicCompletion.ofAlgEquiv I).symm.toRingHom =
      (AdicCompletion.evalₐ I (m + 1)).toRingHom := by
    ext x
    exact AdicCompletion.mk_ofAlgEquiv_symm I (m + 1) x
  rw [he, AdicAffineMorphismLift.evaluation_lift]

end FLT.Mazur.AdicCompleteAffinePoints
