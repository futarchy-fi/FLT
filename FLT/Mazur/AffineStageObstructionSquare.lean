/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionEquiv
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The base-change equivalence for an actual affine stage square

A categorical pushout of the given ring maps supplies the tensor equivalence.
The construction installs the scalar towers from the actual commutative square,
and its right-map calculation identifies the given algebra transition exactly.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.AffineStageObstructionSquare
universe u
variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] (r : R →+* S) (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp r)
  (hp : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom s))

/-- Construct the actual stage's base-change equivalence from its categorical square. -/
def baseChangeEquiv : let _ := r.toAlgebra; S ⊗[R] A ≃ₐ[S] B := by
  let _ := r.toAlgebra
  let _ := s.toAlgebra
  let _ := ((algebraMap S B).comp r).toAlgebra
  let _ : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' hs.symm
  let _ : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp hp
  exact Algebra.IsPushout.equiv R S A B

/-- The constructed equivalence recovers the given original algebra transition. -/
theorem baseChangeEquiv_right (a : A) :
    let _ := r.toAlgebra
    baseChangeEquiv r s hs hp (AffineObstructionBaseChange.rightMap S a) = s a := by
  let _ := r.toAlgebra
  let _ := s.toAlgebra
  let _ := ((algebraMap S B).comp r).toAlgebra
  let _ : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' hs.symm
  let _ : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp hp
  change Algebra.IsPushout.equiv R S A B (1 ⊗ₜ[R] a) = s a
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rfl

include hp in
/-- The original obstruction vanishing gives the actual stage's full ideal test. -/
theorem inclusion_injective (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition r s hs I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := B) (I.map r)) := by
  let _ := r.toAlgebra
  exact AffineObstructionEquiv.inclusion_injective (baseChangeEquiv r s hs hp)
    s hs (baseChangeEquiv_right r s hs hp) I h

end FLT.Mazur.AffineStageObstructionSquare
