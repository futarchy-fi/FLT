/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicConormalTargetCompletion

/-!
# Original conormal maps under square-zero formal presentation maps

Any genuine formal lift over the target algebra map induces a semilinear
map of completed original conormals. Its formula retains actual original
relation representatives inside the completed target kernel.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroFormalConormal

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))

/-- A commuting formal lift defines a genuine morphism of completed extensions. -/
def hom : let _ := e.toAlgebra; (completed P I).Hom (completed Q J) := by
  let _ := e.toAlgebra
  exact
    { toRingHom := f.toRingHom
      toRingHom_algebraMap := f.commutes
      algebraMap_toRingHom := hf }

/-- Formal lifts send actual completed relations to actual completed relations. -/
def kernelMap (x : (completed P I).ker) : (completed Q J).ker :=
  ⟨f x.val, by
    change projection Q J (f x.val) = 0
    rw [hf]
    change e (algebraMap (completed P I).Ring (AdicCompletion I A) x.val) = 0
    rw [x.property, map_zero]⟩

variable [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (hP : P.ker ^ 2 = ⊥) (hQ : Q.ker ^ 2 = ⊥)

/-- The induced conormal map retains the actual formal scalar map. -/
def map : AdicCompletion I P.Cotangent →ₛₗ[e.toRingHom] AdicCompletion J Q.Cotangent := by
  let _ := e.toAlgebra
  let g := (AdicConormalTargetCompletion.equiv Q J hQ).symm.toLinearMap.toAddMonoidHom.comp
    ((Cotangent.map (hom P Q I J e f hf)).toAddMonoidHom.comp
      (AdicConormalTargetCompletion.equiv P I hP).toLinearMap.toAddMonoidHom)
  refine { g with map_smul' := ?_ }
  intro a x
  change (AdicConormalTargetCompletion.equiv Q J hQ).symm
    (Cotangent.map (hom P Q I J e f hf)
      (AdicConormalTargetCompletion.equiv P I hP (a • x))) = _
  rw [map_smul, map_smul]
  change (AdicConormalTargetCompletion.equiv Q J hQ).symm
    (e a • Cotangent.map (hom P Q I J e f hf)
      (AdicConormalTargetCompletion.equiv P I hP x)) = _
  exact (AdicConormalTargetCompletion.equiv Q J hQ).symm.map_smul _ _

/-- The map uses the formal image of each original relation representative. -/
theorem map_of_mk (x : P.ker) :
    map P Q I J e f hf hP hQ (AdicCompletion.of I P.Cotangent (Cotangent.mk x)) =
      (AdicConormalTargetCompletion.equiv Q J hQ).symm
        (Cotangent.mk (kernelMap P Q I J e f hf
          (AdicSquareZeroCompletion.kernelEquiv P I
            (AdicCompletion.of (ideal P I) P.ker x)))) := by
  let _ := e.toAlgebra
  change (AdicConormalTargetCompletion.equiv Q J hQ).symm
    (Cotangent.map (hom P Q I J e f hf)
      (AdicConormalTargetCompletion.equiv P I hP
        (AdicCompletion.of I P.Cotangent (Cotangent.mk x)))) = _
  rw [AdicConormalTargetCompletion.equiv_of_mk, Cotangent.map_mk]
  rfl

end FLT.Mazur.AdicSquareZeroFormalConormal
