/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroFormalHomotopy
public import FLT.Mazur.AdicInfinitesimalOriginalChainMap

/-!
# Explicit homotopies for formal infinitesimal lifts on original complexes

Transport the difference homotopy through both proved infinitesimal
comparisons. The two homotopy identities use completed ORIGINAL conormal
and cotangent modules, and imply independence on degree-one kernels.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalOriginalHomotopy

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f g : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e (projection P.infinitesimal I x))
  (hg : ∀ x, projection Q.infinitesimal J (g x) = e (projection P.infinitesimal I x))
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]

attribute [local instance] AdicInfinitesimalOriginalChainMap.sourceNoetherian
  AdicInfinitesimalOriginalChainMap.targetNoetherian AdicInfinitesimalSpaceMap.finiteSpace

/-- The actual lift difference defines a homotopy between completed ORIGINAL complexes. -/
def homotopy : AdicCompletion I P.CotangentSpace →ₛₗ[e.toRingHom]
    AdicCompletion J Q.Cotangent :=
  (AdicCompletion.congr J (InfinitesimalConormalEquiv.equiv Q)).symm.toLinearMap.comp
    ((AdicSquareZeroFormalHomotopy.homotopy P.infinitesimal Q.infinitesimal I J e f g hf hg
      (InfinitesimalConormalEquiv.ker_square Q)).comp
        (AdicInfinitesimalCotangentSpace.equiv P I).toLinearMap)

omit [IsNoetherianRing P.Ring] in
/-- In degree zero, the original maps differ by the target differential of the homotopy. -/
theorem spaceMap_sub (x : AdicCompletion I P.CotangentSpace) :
    AdicInfinitesimalSpaceMap.map P Q I J e f hf x -
      AdicInfinitesimalSpaceMap.map P Q I J e g hg x =
      AdicCompletion.map J Q.cotangentComplex (homotopy P Q I J e f g hf hg x) := by
  change (AdicInfinitesimalCotangentSpace.equiv Q J).symm _ -
    (AdicInfinitesimalCotangentSpace.equiv Q J).symm _ = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← map_sub]
  have h := LinearMap.congr_fun
    (AdicSquareZeroFormalHomotopy.spaceMap_sub P.infinitesimal Q.infinitesimal I J e f g
      hf hg (InfinitesimalConormalEquiv.ker_square Q))
    (AdicInfinitesimalCotangentSpace.equiv P I x)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  rw [h, AdicInfinitesimalCotangentSpace.inverse_chainMap]
  rfl

/-- In degree one, the original maps differ by the homotopy of the source differential. -/
theorem conormalMap_sub (x : AdicCompletion I P.Cotangent) :
    AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e f hf x -
      AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e g hg x =
      homotopy P Q I J e f g hf hg (AdicCompletion.map I P.cotangentComplex x) := by
  change (AdicCompletion.congr J (InfinitesimalConormalEquiv.equiv Q)).symm _ -
    (AdicCompletion.congr J (InfinitesimalConormalEquiv.equiv Q)).symm _ = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← map_sub, AdicSquareZeroFormalHomotopy.conormalMap_sub]
  have h := LinearMap.congr_fun (AdicInfinitesimalCotangentSpace.chainMap P I) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  change _ = (AdicCompletion.congr J (InfinitesimalConormalEquiv.equiv Q)).symm
    (AdicSquareZeroFormalHomotopy.homotopy P.infinitesimal Q.infinitesimal I J e f g hf hg
      (InfinitesimalConormalEquiv.ker_square Q)
        (AdicInfinitesimalCotangentSpace.equiv P I
          (AdicCompletion.map I P.cotangentComplex x)))
  rw [h]

/-- The induced map on the original first-homology kernel is independent of the formal lift. -/
theorem conormalMap_eq_on_kernel (x : AdicCompletion I P.Cotangent)
    (hx : AdicCompletion.map I P.cotangentComplex x = 0) :
    AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e f hf x =
      AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e g hg x := by
  apply sub_eq_zero.mp
  rw [conormalMap_sub P Q I J e f g hf hg, hx, map_zero]

end FLT.Mazur.AdicInfinitesimalOriginalHomotopy
