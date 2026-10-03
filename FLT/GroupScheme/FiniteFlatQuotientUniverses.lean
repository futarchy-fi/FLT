/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance

/-!
# Finite-flat quotients across point universes

Only the finite point modules are shrunk. The original integral model and
base field remain unchanged, and the result is transported back to the target.
-/

@[expose] public noncomputable section
namespace GaloisModule
universe u v w
variable (R K L : Type u) (X : Type v) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [IsDedekindDomain R] [IsFractionRing R K]
  [IsGalois K L] [IsSepClosed L] [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]

/-- A finite-flat quotient can have a different universe from its integral model. -/
theorem IsFiniteFlat.quotient_universes {Y : Type w} [AddCommGroup Y]
    [DistribMulAction (L ≃ₐ[K] L) Y] (hX : IsFiniteFlat R K L X)
    (q : X →+[L ≃ₐ[K] L] Y) (hq : Function.Surjective q) :
    IsFiniteFlat R K L Y := by
  let : Finite X := hX.finite R K L X
  let : Finite Y := Finite.of_surjective q hq
  let eX : Shrink.{u} X ≃+ X := Shrink.addEquiv
  let eY : Shrink.{u} Y ≃+ Y := Shrink.addEquiv
  let : DistribMulAction (L ≃ₐ[K] L) (Shrink.{u} X) := eX.distribMulAction _
  let : DistribMulAction (L ≃ₐ[K] L) (Shrink.{u} Y) := eY.distribMulAction _
  let f : X →+[L ≃ₐ[K] L] Shrink.{u} X :=
    { eX.symm.toAddMonoidHom with
      map_smul' := by
        intro g x
        change eX.symm (g • x) = eX.symm (g • eX (eX.symm x))
        rw [eX.apply_symm_apply] }
  let q' : Shrink.{u} X →+[L ≃ₐ[K] L] Shrink.{u} Y :=
    { (eY.symm.toAddMonoidHom.comp q.toAddMonoidHom).comp eX.toAddMonoidHom with
      map_smul' := by
        intro g x
        change eY.symm (q (eX (eX.symm (g • eX x)))) =
          eY.symm (g • eY (eY.symm (q (eX x))))
        rw [eX.apply_symm_apply, eY.apply_symm_apply, map_smul] }
  let t : Shrink.{u} Y →+[L ≃ₐ[K] L] Y :=
    { eY.toAddMonoidHom with
      map_smul' := by
        intro g y
        exact eY.apply_symm_apply (g • eY y) }
  have hs := hX.map R K L X f eX.symm.bijective
  exact (hs.quotient R K L (Shrink.{u} X) q'
    (eY.symm.surjective.comp (hq.comp eX.surjective))).map R K L _ t eY.bijective

end GaloisModule
