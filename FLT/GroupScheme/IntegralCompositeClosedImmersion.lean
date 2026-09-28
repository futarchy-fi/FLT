/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualAugmentation
public import FLT.GroupScheme.FaithfullyFlatQuotient
public import FLT.GroupScheme.FaithfullyFlatRetraction

/-!
# Closed immersions in composite quotient diagrams

Cartier duality identifies the descended inclusion with a base change of the
dual outer quotient. Faithful flatness of that base change gives a linear
retraction; dualizing it proves that the original inclusion is closed.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open HopfAlgebra.CartierDual

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]

/-- A faithfully flat Cartier transpose makes the original coordinate map surjective. -/
theorem FiniteFlatObject.Hom.surjectiveOfDualFaithfullyFlat
    {X Y : FiniteFlatObject R} (f : X.Hom Y)
    (hf : f.cartierDual.toAlgHom.toRingHom.FaithfullyFlat) : Function.Surjective f := by
  let dualAlgebra := f.cartierDual.toAlgHom.toRingHom.toAlgebra
  let dualTower : IsScalarTower R X.cartierDual.model.CoordinateRing
      Y.cartierDual.model.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' f.cartierDual.toAlgHom.comp_algebraMap.symm
  let dualFlat : Module.FaithfullyFlat X.cartierDual.model.CoordinateRing
      Y.cartierDual.model.CoordinateRing := hf
  obtain ⟨s, hs⟩ := Algebra.faithfullyFlatLinearRetraction
    (R := R) (A := X.cartierDual.model.CoordinateRing)
      (B := Y.cartierDual.model.CoordinateRing)
  intro x
  let l : Module.Dual R (HopfAlgebra.CartierDual R Y.model.CoordinateRing) :=
    (Module.Dual.eval R X.model.CoordinateRing x).comp
      ((linearEquiv (R := R) (A := X.model.CoordinateRing)).toLinearMap.comp s)
  obtain ⟨y, hy⟩ := (bidualLinearEquiv (R := R) (A := Y.model.CoordinateRing)).surjective
    (WithConv.toConv l)
  refine ⟨y, ?_⟩
  apply (Module.evalEquiv R X.model.CoordinateRing).injective
  ext φ
  have he := congrArg (fun k : HopfAlgebra.CartierDual R
    (HopfAlgebra.CartierDual R Y.model.CoordinateRing) ↦
      k (f.cartierDual (WithConv.toConv φ))) hy
  change φ (f y) =
    (show HopfAlgebra.CartierDual R X.model.CoordinateRing from
      s (f.cartierDual (WithConv.toConv φ))) x at he
  have hsφ := LinearMap.congr_fun hs (WithConv.toConv φ)
  change s (f.cartierDual (WithConv.toConv φ)) = WithConv.toConv φ at hsφ
  change φ (f y) = φ x
  simpa only [hsφ] using he

/-- A compatible map of quotients by the same inner kernel is a closed immersion
when the outer intermediate model is an actual integral kernel. -/
theorem descendedIntegralInclusionSurjective
    {A B C H Q T : FiniteFlatObject R}
    (E₁ : FiniteFlatExtension A B C) (E₂ : FiniteFlatExtension B H Q)
    (E : FiniteFlatExtension A H T) (i : C.Hom T)
    (hi : E.inclusion = E₁.inclusion.comp E₂.inclusion)
    (hc : E₁.quotient.comp i = E₂.inclusion.comp E.quotient) : Function.Surjective i := by
  apply i.surjectiveOfDualFaithfullyFlat
  let f := E₂.inclusion.cartierDual.toAlgHom.toRingHom
  let I := HopfAlgebra.augmentationIdeal E₁.inclusion.cartierDual
  let J := HopfAlgebra.augmentationIdeal E.inclusion.cartierDual
  have hcomp : E.inclusion.cartierDual.toAlgHom.toRingHom =
      f.comp E₁.inclusion.cartierDual.toAlgHom.toRingHom := by
    ext φ
    apply WithConv.ext
    ext x
    change (show HopfAlgebra.CartierDual R A.model.CoordinateRing from φ) (E.inclusion x) =
      (show HopfAlgebra.CartierDual R A.model.CoordinateRing from φ)
        (E₁.inclusion (E₂.inclusion x))
    rw [hi]
    rfl
  have hJ : J = I.map f := by
    dsimp [I, J, HopfAlgebra.augmentationIdeal]
    rw [Ideal.map_map]
    exact congrArg (fun g ↦ Ideal.map g _) hcomp
  have hIJ : I ≤ J.comap f := by rw [hJ]; exact Ideal.le_comap_map
  let j := Ideal.quotientMap J f hIJ
  have hj : j.FaithfullyFlat := RingHom.FaithfullyFlat.quotientMap f
    E₂.dualQuotientFaithfullyFlat I J hJ hIJ
  have he : i.cartierDual.toAlgHom.toRingHom = E.dualKernelEquiv.toRingEquiv.toRingHom.comp
      (j.comp E₁.dualKernelEquiv.symm.toRingEquiv.toRingHom) := by
    ext c
    obtain ⟨z, rfl⟩ := E₁.dualKernelEquiv.surjective c
    obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
    change i.cartierDual (E₁.dualKernelEquiv _) =
      E.dualKernelEquiv (j (E₁.dualKernelEquiv.symm (E₁.dualKernelEquiv _)))
    rw [AlgEquiv.symm_apply_apply]
    apply WithConv.ext
    ext t
    exact congrArg (show HopfAlgebra.CartierDual R B.model.CoordinateRing from φ)
      (DFunLike.congr_fun hc t)
  rw [he]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective E₁.dualKernelEquiv.symm.bijective) hj)
    (RingHom.FaithfullyFlat.of_bijective E.dualKernelEquiv.bijective)

end ThreeAdicPlan
