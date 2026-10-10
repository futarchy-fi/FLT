/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartUnitLift
public import FLT.Mazur.WeierstrassFourPairAssociativity

/-!
# Four infinity laws with invertible input Z coordinates

The equations only match the real inputs and individual outputs of each law.
Five coordinate units give affine presentations and hence equality of the final
outputs. The final output coordinates themselves need not be units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
include hΔ

/-- Four compatible infinity charts associate once the five input Z coordinates are units. -/
theorem infinityFourLaw_eq_of_affine {X : Scheme.{u}}
    (p : Fin 7 → (X ⟶ chartScheme W 1))
    (f : Fin 4 → (X ⟶ Spec (.of (InfinityAdditionOpen W))))
    (hl : ∀ j, f j ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
      p (infinityTripleLeftIndex j))
    (hr : ∀ j, f j ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      p (infinityTripleRightIndex j))
    (ho : ∀ j, f j ≫ infinityAdditionSpec W = p (infinityTripleOutputIndex j))
    (hu : ∀ i : Fin 5, IsUnit (specSectionHom (p (i.castAdd 2)) (coord W 1 2))) :
    p 5 = p 6 := by
  apply (cancel_mono (integralCurveChart W 1)).mp
  apply integralCurveFourPairs_assoc W hΔ
    (fun i => p i ≫ integralCurveChart W 1) (fun j => f j ≫ infinityGlobalDomain W)
  · intro j
    rw [Category.assoc, infinityGlobalDomain_fst, ← Category.assoc, hl]
  · intro j
    rw [Category.assoc, infinityGlobalDomain_snd, ← Category.assoc, hr]
  · intro j
    rw [Category.assoc, infinityGlobalDomain_addition, ← Category.assoc, ho]
  · intro i
    exact exists_chart_of_coordinate_unit W 1 2 _ (hu i)

/-- The same result applies to compatible algebra specializations into any commutative ring. -/
theorem infinityFourLaw_algHom_eq_of_units {S : Type u} [CommRing S] [Algebra R S]
    (p : Fin 7 → (Coordinate W 1 →ₐ[R] S))
    (f : Fin 4 → (InfinityAdditionOpen W →ₐ[R] S))
    (hl : ∀ j, (f j).comp (infinityInputLeft W) = p (infinityTripleLeftIndex j))
    (hr : ∀ j, (f j).comp (infinityInputRight W) = p (infinityTripleRightIndex j))
    (ho : ∀ j, (f j).comp (infinityAdditionChart W) = p (infinityTripleOutputIndex j))
    (hu : ∀ i : Fin 5, IsUnit (p (i.castAdd 2) (coord W 1 2))) : p 5 = p 6 := by
  have he := infinityFourLaw_eq_of_affine W hΔ
    (fun i => Spec.map (CommRingCat.ofHom (p i).toRingHom))
    (fun j => Spec.map (CommRingCat.ofHom (f j).toRingHom))
    (fun j => by
      rw [← Spec.map_comp]
      exact congrArg (fun a => Spec.map (CommRingCat.ofHom a.toRingHom)) (hl j))
    (fun j => by
      rw [← Spec.map_comp]
      exact congrArg (fun a => Spec.map (CommRingCat.ofHom a.toRingHom)) (hr j))
    (fun j => by
      rw [infinityAdditionSpec, ← Spec.map_comp]
      exact congrArg (fun a => Spec.map (CommRingCat.ofHom a.toRingHom)) (ho j))
    (fun i => by
      rw [show Spec.map (CommRingCat.ofHom (p (i.castAdd 2)).toRingHom) =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (p (i.castAdd 2)).toRingHom) from
          (Category.id_comp _).symm, specSectionHom_comp]
      exact (hu i).map (specSectionHom (𝟙 _)))
  apply AlgHom.coe_ringHom_injective
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

end FLT.Mazur.WeierstrassIntegralChart
