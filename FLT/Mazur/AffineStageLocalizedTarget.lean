/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStageObstructionSquare
public import FLT.Mazur.AffineTargetObstructionTransition
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Transporting actual stage target localizations through the pushout equivalence

The canonical categorical stage equivalence makes a localization of the actual
stage algebra into a localization of its tensor presentation. The old algebra
map is preserved, so obstruction vanishing is tested in the same final target.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.AffineStageLocalizedTarget
open AffineStageObstructionSquare
universe u
variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] (r : R →+* S) (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp r)
  (hp : IsPushout (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom s))
  (T : Type*) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower S B T]

/-- The actual target extension, viewed as an algebra over the tensor presentation. -/
@[instance_reducible] def tensorAlgebra : let _ := r.toAlgebra; Algebra (S ⊗[R] A) T := by
  let _ := r.toAlgebra
  exact ((algebraMap B T).comp (baseChangeEquiv r s hs hp).toRingHom).toAlgebra

/-- Transport retains the given scalar action of the new base on the target. -/
theorem tensorScalarTower :
    let _ := r.toAlgebra
    let _ := tensorAlgebra r s hs hp T
    IsScalarTower S (S ⊗[R] A) T := by
  let _ := r.toAlgebra
  let _ := tensorAlgebra r s hs hp T
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap S T x = algebraMap B T
    (baseChangeEquiv r s hs hp (algebraMap S (S ⊗[R] A) x))
  rw [(baseChangeEquiv r s hs hp).commutes]
  exact IsScalarTower.algebraMap_apply S B T x

omit [Algebra S T] [IsScalarTower S B T] in
/-- The tensor presentation still maps the old algebra by its actual stage transition. -/
theorem tensorRightMap_eq :
    let _ := r.toAlgebra
    let _ := tensorAlgebra r s hs hp T
    AffineTargetObstructionTransition.rightMap (R := R) S T = (algebraMap B T).comp s := by
  let _ := r.toAlgebra
  let _ := tensorAlgebra r s hs hp T
  ext a
  change algebraMap B T
    (baseChangeEquiv r s hs hp (AffineObstructionBaseChange.rightMap S a)) = _
  rw [baseChangeEquiv_right]
  rfl

omit [Algebra S T] [IsScalarTower S B T] in
/-- Flat extensions of the actual stage are flat over its tensor presentation. -/
theorem tensor_flat [Module.Flat B T] :
    let _ := r.toAlgebra
    let _ := tensorAlgebra r s hs hp T
    Module.Flat (S ⊗[R] A) T := by
  let _ := r.toAlgebra
  exact (RingHom.Flat.of_bijective (baseChangeEquiv r s hs hp).bijective).comp
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat B T))

omit [Algebra S T] [IsScalarTower S B T] in
/-- The actual localization is transported by the inverse image of its denominators. -/
theorem tensor_isLocalization (U : Submonoid B) [IsLocalization U T] :
    let _ := r.toAlgebra
    let _ := tensorAlgebra r s hs hp T
    IsLocalization (U.comap (baseChangeEquiv r s hs hp).toMonoidHom) T := by
  let _ := r.toAlgebra
  let _ := tensorAlgebra r s hs hp T
  apply IsLocalization.of_ringEquiv_left (baseChangeEquiv r s hs hp).toRingEquiv
    (Submonoid.map_comap_eq_of_surjective (baseChangeEquiv r s hs hp).surjective U)
  intro x
  rfl

end FLT.Mazur.AffineStageLocalizedTarget
