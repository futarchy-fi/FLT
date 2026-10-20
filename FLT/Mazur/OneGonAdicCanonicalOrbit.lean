/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCanonicalSubgroup
public import FLT.Mazur.RootsOfUnityIntrinsicOrbit
public import FLT.Mazur.CartierSectionProductRank

/-!
# The full cyclotomic orbit on the constructed adic subgroup

Whenever the base carries the specialized cyclotomic coordinate, its actual
section lies in the constructed subgroup. The ambient orbit divisor contains
the entire subgroup and has the same finite locally free degree, even at
singular fibers and when roots coincide.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.OneGonAdicCharacterTower

open ArithmeticOneGonGeneralizedCurve IntegralCyclotomicCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (φ : Coordinate n →+* R)

/-- The cyclotomic section in the actual constructed complete-base subgroup. -/
def canonicalGenerator : 𝟙_ (Over (Spec (.of R))) ⟶
    (canonicalFiniteSubgroup I t ht n).carrier := RootsOfUnityIntrinsicOrbit.generator n φ

/-- The section satisfies the exact original torsion relation. -/
theorem canonicalGenerator_pow : canonicalGenerator I t ht n φ ^ n = 1 :=
  RootsOfUnityIntrinsicOrbit.generator_pow n φ

/-- The entire constructed subgroup lies in its full generator-orbit divisor. -/
theorem canonicalGenerator_orbit_le :
    ∏ k : Fin n, ((canonicalGenerator I t ht n φ ^ k.val) ≫
      (canonicalFiniteSubgroup I t ht n).curveMap).left.ker ≤
        (canonicalFiniteSubgroup I t ht n).ideal := by
  let E := curve t (complementaryFactor_isUnit I t ht)
  let H := canonicalFiniteSubgroup I t ht n
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : ∀ k : Fin n, IsClosedImmersion
      ((RootsOfUnityIntrinsicOrbit.generator n φ ^ k.val).left ≫ H.curveMap.left) := fun k ↦
    FCurve.isClosedImmersion_section E.curve.hom
      ((canonicalGenerator I t ht n φ ^ k.val) ≫ H.curveMap).left (Over.w _)
  exact RootsOfUnityIntrinsicOrbit.ambient_orbit_le n φ H.curveMap.left

/-- The full orbit divisor on the original, possibly singular curve has exact rank n. -/
theorem canonicalGenerator_orbit_degree :
    FCurve.FiniteLocallyFreeDegree
      ((∏ k : Fin n, ((canonicalGenerator I t ht n φ ^ k.val) ≫
        (canonicalFiniteSubgroup I t ht n).curveMap).left.ker).subschemeι ≫
          (curve t (complementaryFactor_isUnit I t ht)).curve.hom) n := by
  let E := curve t (complementaryFactor_isUnit I t ht)
  let H := canonicalFiniteSubgroup I t ht n
  let a := fun k : Fin n ↦ ((canonicalGenerator I t ht n φ ^ k.val) ≫ H.inclusion).left
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : LocallyOfFinitePresentation E.curve.hom := E.family.family.2.2
  have hd : SmoothOfRelativeDimension 1 E.group.hom :=
    WeierstrassIntegralChart.integralSmoothStructure_relativeDimension (OneGonSmoothing.equation t)
  let _ : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [Over.w]
    exact hd
  have h := FCurve.finiteLocallyFreeDegree_smoothOpen_section_prod E.curve.hom
    (Finset.univ : Finset (Fin n)) E.inclusion.left a (fun k ↦ by
      rw [← Category.assoc]
      exact Over.w (((canonicalGenerator I t ht n φ ^ k.val) ≫ H.inclusion) ≫ E.inclusion))
  have he (k : Fin n) : a k ≫ E.inclusion.left =
      ((canonicalGenerator I t ht n φ ^ k.val) ≫ H.curveMap).left := by
    change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    exact Category.assoc _ _ _
  have hI : (∏ k : Fin n, (a k ≫ E.inclusion.left).ker) =
      ∏ k : Fin n, ((canonicalGenerator I t ht n φ ^ k.val) ≫ H.curveMap).left.ker := by
    apply Finset.prod_congr rfl
    intro k _
    exact congrArg Scheme.Hom.ker (he k)
  rw [hI] at h
  simpa only [Finset.card_univ, Fintype.card_fin] using h

end FLT.Mazur.OneGonAdicCharacterTower
