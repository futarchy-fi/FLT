/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapPullback

/-!
# Tensor coordinates for a geometric overlap isomorphism

An isomorphism between actual projection pullbacks induces an `S`-linear
isomorphism between the two tensor coefficient modules. Compatibility with
the other copy of `S` is proved from sheaf linearity, not supplied as data.
Diagonal and triple-overlap coherence are separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]

/-- Restrict coefficient scalars along the base algebra map. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- An actual isomorphism of the projection sheaves on the tensor spectrum. -/
abbrev Overlap :=
  (pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M ≅
    (pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M

variable (e : Overlap R S M)

/-- The additive coefficient comparison associated to an actual sheaf isomorphism. -/
def tensorAddEquiv : coefficients S M ⊗[R] S ≃+ S ⊗[R] coefficients S M :=
  (firstSections R S M).trans
    ((moduleSpecΓFunctor.mapIso e).toLinearEquiv.toAddEquiv.trans (secondSections R S M).symm)

/-- The coordinate isomorphism reconstructs the given section map exactly. -/
theorem tensorAddEquiv_sections (x : coefficients S M ⊗[R] S) :
    secondSections R S M (tensorAddEquiv R S M e x) =
      (moduleSpecΓFunctor.map e.hom) (firstSections R S M x) :=
  (secondSections R S M).apply_symm_apply _

/-- Sheaf linearity supplies the first scalar action on overlap coordinates. -/
theorem tensorAddEquiv_smul (s : S) (x : coefficients S M ⊗[R] S) :
    tensorAddEquiv R S M e (s • x) = s • tensorAddEquiv R S M e x := by
  apply (secondSections R S M).injective
  rw [tensorAddEquiv_sections, secondSections_smul, firstSections_smul,
    tensorAddEquiv_sections]
  exact (moduleSpecΓFunctor.map e.hom).hom.map_smul _ _

/-- The geometric overlap isomorphism in tensor coordinates, linear over the first scalar. -/
def tensorEquiv : coefficients S M ⊗[R] S ≃ₗ[S] S ⊗[R] coefficients S M :=
  { tensorAddEquiv R S M e with map_smul' := tensorAddEquiv_smul R S M e }

/-- The section reconstruction square for the linear coefficient isomorphism. -/
theorem tensorEquiv_sections (x : coefficients S M ⊗[R] S) :
    secondSections R S M (tensorEquiv R S M e x) =
      (moduleSpecΓFunctor.map e.hom) (firstSections R S M x) :=
  tensorAddEquiv_sections R S M e x

/-- The other scalar law follows from the full overlap-ring linearity of the sheaf map. -/
theorem tensorEquiv_other_smul (n : coefficients S M) (s t : S) :
    tensorEquiv R S M e (n ⊗ₜ[R] (s * t)) =
      (Algebra.lsmul R R (coefficients S M) s).lTensor S
        (tensorEquiv R S M e (n ⊗ₜ[R] t)) := by
  apply (secondSections R S M).injective
  rw [tensorEquiv_sections, secondSections_other_smul, tensorEquiv_sections]
  have h := firstSections_smul_tmul R S M 1 s t n
  simp only [one_smul] at h
  rw [h]
  exact (moduleSpecΓFunctor.map e.hom).hom.map_smul _ _

/-- Move an isomorphism on the actual fiber product to its tensor-spectrum chart. -/
def fromFiberProduct
    (e : (pullback (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M ≅
      (pullback (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M) : Overlap R S M :=
  (firstProjectionIso R S M).symm ≪≫
    (pullback (pullbackSpecIso R S S).inv).mapIso e ≪≫ secondProjectionIso R S M

end FLT.Mazur.AffineGeometricOverlap
