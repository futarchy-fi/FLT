/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTripleEvaluation

/-!
# Additive extension of the direct triple-coordinate formulas

Use the pair charts' restricted coefficient instance for the direct chart.
Abstract additive diagrams extend its pure-tensor formulas without unfolding
the sheaf module structures in an induction proof.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleAdditivity
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback AffineDirectTripleSections AffineTensorCocycle
open AffineIteratedPullbackSections AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem outer_ext {A B C N P Q : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] [AddCommGroup P] [AddCommGroup Q]
    [DistribSMul C P] (D : B ⊗[A] (B ⊗[A] N) ≃+ P) (K : B ⊗[A] N ≃+ Q)
    (G : Q →+ P) (s : B) (c : C)
    (h : ∀ t n, D (s ⊗ₜ[A] (t ⊗ₜ[A] n)) = c • G (K (t ⊗ₜ[A] n)))
    (x : B ⊗[A] N) : D (s ⊗ₜ[A] x) = c • G (K x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t n => exact h t n
  | add x y hx hy => simp only [tmul_add, map_add, smul_add, hx, hy]

private theorem middle_ext {A B C N P Q : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] [AddCommGroup P] [AddCommGroup Q]
    [DistribSMul C P] (D : B ⊗[A] (B ⊗[A] N) ≃+ P) (K : B ⊗[A] N ≃+ Q)
    (G : Q →+ P) (s : B) (c : C)
    (h : ∀ t n, D (insertMiddle s (t ⊗ₜ[A] n)) = c • G (K (t ⊗ₜ[A] n)))
    (x : B ⊗[A] N) : D (insertMiddle s x) = c • G (K x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t n => exact h t n
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The direct chart with the same restricted coefficient instance as the pair charts. -/
def sections : S ⊗[R] (S ⊗[R] coefficients S M) ≃+
    moduleSpecΓFunctor.obj (coordinate R S M (coord3 R S)) :=
  (extension R S (coefficients S M)).symm.trans
    (AffineModulePullbackSections.sectionsIso
      (CommRingCat.ofHom (coord3 R S)) M).toLinearEquiv.toAddEquiv

/-- The direct chart evaluates pure tensors using the third-coordinate unit. -/
theorem sections_tmul (a b : S) (n : coefficients S M) :
    sections R S M (a ⊗ₜ[R] (b ⊗ₜ[R] n)) =
      (a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) • specUnit (CommRingCat.ofHom (coord3 R S)) M n :=
  AffineModulePullbackSections.sectionsIso_tmul (CommRingCat.ofHom (coord3 R S)) M _ n

/-- The outer scalar multiplies the normalized last-pair pullback. -/
theorem directSections_outer_tmul (s t : S) (n : coefficients S M) :
  sections R S M (s ⊗ₜ[R] (t ⊗ₜ[R] n)) =
    (s ⊗ₜ[R] (1 : S ⊗[R] S)) •
      mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
        (comparison (right R S) (pair23 R S).toRingHom
          (coord3 R S) (pair23_right R S) M).hom (secondSections R S M (t ⊗ₜ[R] n)) := by
  have h := second_normalized R S M (pair23 R S).toRingHom
    (coord3 R S) (pair23_right R S) n t
  rw [h, sections_tmul, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord3 R S)) M n)
  change s ⊗ₜ[R] (t ⊗ₜ[R] (1 : S)) =
    (s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S))) *
      ((1 : S) ⊗ₜ[R] (t ⊗ₜ[R] (1 : S)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Inserting a middle scalar is the normalized outer-pair pullback. -/
theorem directSections_insertMiddle_tmul (s a : S) (n : coefficients S M) :
  sections R S M (insertMiddle s (a ⊗ₜ[R] n)) =
    coord2 R S s •
      mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
        (comparison (right R S) (pair13 R S).toRingHom
          (coord3 R S) (pair13_right R S) M).hom (secondSections R S M (a ⊗ₜ[R] n)) := by
  change sections R S M (a ⊗ₜ[R] (s ⊗ₜ[R] n)) = _
  have h := second_normalized R S M (pair13 R S).toRingHom
    (coord3 R S) (pair13_right R S) n a
  rw [sections_tmul, h, smul_smul]
  apply congrArg (· • specUnit (CommRingCat.ofHom (coord3 R S)) M n)
  change a ⊗ₜ[R] (s ⊗ₜ[R] (1 : S)) =
    ((1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (1 : S))) *
      (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The outer scalar multiplies the normalized last-pair pullback. -/
theorem directSections_outer (s : S) (x : S ⊗[R] coefficients S M) :
    sections R S M (s ⊗ₜ[R] x) =
      (s ⊗ₜ[R] (1 : S ⊗[R] S)) •
        mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
          (comparison (right R S) (pair23 R S).toRingHom
            (coord3 R S) (pair23_right R S) M).hom (secondSections R S M x) :=
  outer_ext (sections R S M) (secondSections R S M)
    (mappedUnit (CommRingCat.ofHom (pair23 R S).toRingHom) _
      (comparison (right R S) (pair23 R S).toRingHom
        (coord3 R S) (pair23_right R S) M).hom) s _
    (directSections_outer_tmul R S M s) x

/-- Inserting a middle scalar is the normalized outer-pair pullback. -/
theorem directSections_insertMiddle (s : S) (x : S ⊗[R] coefficients S M) :
    sections R S M (insertMiddle s x) =
      coord2 R S s •
        mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
          (comparison (right R S) (pair13 R S).toRingHom
            (coord3 R S) (pair13_right R S) M).hom (secondSections R S M x) :=
  middle_ext (sections R S M) (secondSections R S M)
    (mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
      (comparison (right R S) (pair13 R S).toRingHom
        (coord3 R S) (pair13_right R S) M).hom) s _
    (directSections_insertMiddle_tmul R S M s) x

end FLT.Mazur.AffineDirectTripleAdditivity
