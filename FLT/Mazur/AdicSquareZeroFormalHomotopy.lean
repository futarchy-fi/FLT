/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalLiftDifference
public import FLT.Mazur.AdicSquareZeroFormalChainMap

/-!
# Difference homotopies on completed original square-zero complexes

The explicit formal lift difference lands in the completed ORIGINAL
conormal module. Both degrees of the original complex satisfy the
homotopy identities.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroFormalHomotopy

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f g : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  (hg : ∀ x, projection Q J (g x) = e (projection P I x))
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]
  [IsNoetherianRing Q.Ring] (hQ : Q.ker ^ 2 = ⊥)

/-- The actual difference of lifts gives a homotopy valued in completed original conormals. -/
def homotopy : AdicCompletion I P.CotangentSpace →ₛₗ[e.toRingHom]
    AdicCompletion J Q.Cotangent :=
  (AdicConormalTargetCompletion.equiv Q J hQ).symm.toLinearMap.comp
    (AdicFormalLiftDifference.formalHomotopy P Q I J e f g hf hg)

/-- Each original differential evaluates to the actual conormal difference of the lifts. -/
theorem homotopy_of_tmul (a : A) (x : P.Ring) :
    homotopy P Q I J e f g hf hg hQ (AdicCompletion.of I P.CotangentSpace
      (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        e (AdicCompletion.of I A a) • (AdicConormalTargetCompletion.equiv Q J hQ).symm
          (Cotangent.mk (AdicFormalLiftDifference.difference P Q I J e f g hf hg x)) := by
  change (AdicConormalTargetCompletion.equiv Q J hQ).symm
    (AdicFormalLiftDifference.formalHomotopy P Q I J e f g hf hg _) = _
  rw [AdicFormalLiftDifference.formalHomotopy_of_tmul, map_smul]

/-- The degree-zero difference on original tensors is the differential of the homotopy. -/
theorem spaceMap_sub_of_tmul (a : A) (x : P.Ring) :
    AdicFormalCotangentSpaceMap.map P Q I J e f hf
        (AdicCompletion.of I P.CotangentSpace (a ⊗ₜ KaehlerDifferential.D R P.Ring x)) -
      AdicFormalCotangentSpaceMap.map P Q I J e g hg
        (AdicCompletion.of I P.CotangentSpace (a ⊗ₜ KaehlerDifferential.D R P.Ring x)) =
      AdicCompletion.map J Q.cotangentComplex
        (homotopy P Q I J e f g hf hg hQ
          (AdicCompletion.of I P.CotangentSpace
            (a ⊗ₜ KaehlerDifferential.D R P.Ring x))) := by
  rw [AdicFormalCotangentSpaceMap.map_of_tmul, AdicFormalCotangentSpaceMap.map_of_tmul,
    homotopy_of_tmul, map_smul, ← AdicSquareZeroComplexComparison.derivation_kernel,
    ← smul_sub, ← map_sub]
  rfl

/-- The degree-zero maps differ by the target differential of the explicit homotopy. -/
theorem spaceMap_sub :
    AdicFormalCotangentSpaceMap.map P Q I J e f hf -
        AdicFormalCotangentSpaceMap.map P Q I J e g hg =
      (AdicCompletion.map J Q.cotangentComplex).comp
        (homotopy P Q I J e f g hf hg hQ) := by
  let _ : Module (AdicCompletion I A) (AdicCompletion J Q.CotangentSpace) :=
    Module.compHom _ e.toRingHom
  let N := AdicCompletion J Q.CotangentSpace
  let _ := AdicPresentationScalarTowers.targetTower Q J
  let _ : Module A N := Module.compHom _ (algebraMap A (AdicCompletion I A))
  let _ : Module P.Ring N := Module.compHom _ (algebraMap P.Ring A)
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R P.Ring N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (algebraMap A (AdicCompletion I A)
        (algebraMap P.Ring A (algebraMap R P.Ring r))) • x = r • x
      rw [← IsScalarTower.algebraMap_apply R P.Ring A,
        ← IsScalarTower.algebraMap_apply R A (AdicCompletion I A), e.commutes,
        algebraMap_smul]
  let lhs := AdicFormalCotangentSpaceMap.map P Q I J e f hf -
    AdicFormalCotangentSpaceMap.map P Q I J e g hg
  let rhs := (AdicCompletion.map J Q.cotangentComplex).comp
    (homotopy P Q I J e f g hf hg hQ)
  let lhs' : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A]
      AdicCompletion J Q.CotangentSpace :=
    { lhs.toAddHom with map_smul' := fun a x ↦ lhs.map_smulₛₗ a x }
  let rhs' : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A]
      AdicCompletion J Q.CotangentSpace :=
    { rhs.toAddHom with map_smul' := fun a x ↦ rhs.map_smulₛₗ a x }
  have h : lhs' = rhs' := by
    apply AdicCotangentSpaceLift.ext P I
    intro x
    exact spaceMap_sub_of_tmul P Q I J e f g hf hg hQ 1 x
  exact LinearMap.ext fun x ↦ LinearMap.congr_fun h x

variable [IsNoetherianRing P.Ring] (hP : P.ker ^ 2 = ⊥)

/-- The degree-one homotopy identity retains each original relation representative. -/
theorem conormalMap_sub_of_mk (x : P.ker) :
    AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ
        (AdicCompletion.of I P.Cotangent (Cotangent.mk x)) -
      AdicSquareZeroFormalConormal.map P Q I J e g hg hP hQ
        (AdicCompletion.of I P.Cotangent (Cotangent.mk x)) =
      homotopy P Q I J e f g hf hg hQ
        (AdicCompletion.map I P.cotangentComplex
          (AdicCompletion.of I P.Cotangent (Cotangent.mk x))) := by
  rw [AdicCompletion.map_of, cotangentComplex_mk, homotopy_of_tmul]
  change _ = e 1 • _
  rw [map_one, one_smul, AdicSquareZeroFormalConormal.map_of_mk,
    AdicSquareZeroFormalConormal.map_of_mk, ← map_sub, ← map_sub]
  congr 2

/-- The degree-one maps differ by the homotopy of the source differential. -/
theorem conormalMap_sub (x : AdicCompletion I P.Cotangent) :
    AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ x -
      AdicSquareZeroFormalConormal.map P Q I J e g hg hP hQ x =
      homotopy P Q I J e f g hf hg hQ (AdicCompletion.map I P.cotangentComplex x) := by
  let _ := Cotangent.finite P.ker.fg_of_isNoetherianRing
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I P.Cotangent x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a x
    rw [AdicCompletion.ofTensorProduct_tmul, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, ← smul_sub]
    congr 1
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    exact conormalMap_sub_of_mk P Q I J e f g hf hg hQ hP x
  · intro x y hx hy
    simp only [map_add, add_sub_add_comm, hx, hy]

end FLT.Mazur.AdicSquareZeroFormalHomotopy
