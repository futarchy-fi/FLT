/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricFiniteSubgroupHopfRank
public import FLT.Mazur.LaurentHopfRootsScheme

/-!
# Arbitrary finite subgroups of a toric generalized curve are roots of unity

The original carrier is isomorphic to the roots scheme of the prescribed rank.
The comparison preserves its actual inclusion and therefore its entire divisor,
without assuming etaleness or that the rank is invertible in the field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.ToricFiniteSubgroupRootsClassification

section Coordinates

variable {K A : Type} [Field K] [CommRing A] [HopfAlgebra K A]
  (f : K[T;T⁻¹] →ₐc[K] A) (hf : Function.Surjective f)
  (n : ℕ) (hn : Module.finrank K A = n)

/-- The affine roots comparison at an independently specified subgroup rank. -/
def comparisonOfRank : LaurentHopfRootsScheme.model (K := K) (A := A) ≅
    RootsOfUnityScheme.model K n :=
  hn ▸ LaurentHopfRootsScheme.comparison f hf

instance comparisonOfRank_isMonHom : IsMonHom (comparisonOfRank f hf n hn).hom := by
  subst n
  exact LaurentHopfRootsScheme.comparison_isMonHom f hf

/-- The rank-indexed comparison retains the given full quotient inclusion. -/
theorem comparisonOfRank_inclusion :
    (comparisonOfRank f hf n hn).hom ≫ RootsOfUnityScheme.inclusion K n =
      LaurentHopfRootsScheme.inclusion f := by
  subst n
  exact LaurentHopfRootsScheme.comparison_inclusion f hf

end Coordinates

open GeneralizedEllipticCurve ToricFiniteSubgroupHopfPresentation

variable {K : Type} [Field K] {E : GeneralizedEllipticCurve (Spec (.of K))}
  {n : ℕ} (H : E.FiniteSubgroup n)
  (e : MultiplicativeGroupScheme.gm K ≅ E.group) [IsMonHom e.hom]

/-- Every original toric finite subgroup is the roots scheme of its actual prescribed rank. -/
def rootsIso : H.carrier ≅ RootsOfUnityScheme.model K n :=
  (carrierIso H).symm ≪≫ comparisonOfRank (restriction H e) (restriction_surjective H e)
    n (coordinates_finrank H)

instance rootsIso_isMonHom : IsMonHom (rootsIso H e).hom := by
  change IsMonHom ((carrierIso H).inv ≫
    (comparisonOfRank (restriction H e) (restriction_surjective H e)
      n (coordinates_finrank H)).hom)
  infer_instance

/-- The comparison is compatible with the original entire subgroup inclusion. -/
theorem rootsIso_inclusion :
    (rootsIso H e).hom ≫ RootsOfUnityScheme.inclusion K n ≫ e.hom = H.inclusion := by
  change ((carrierIso H).inv ≫
    (comparisonOfRank (restriction H e) (restriction_surjective H e)
      n (coordinates_finrank H)).hom) ≫ _ = _
  rw [Category.assoc, ← Category.assoc
    (comparisonOfRank (restriction H e) (restriction_surjective H e)
      n (coordinates_finrank H)).hom, comparisonOfRank_inclusion]
  have h : LaurentHopfRootsScheme.inclusion (restriction H e) =
      (carrierIso H).hom ≫ torusMap H e := by
    apply Over.OverMorphism.ext
    exact restriction_spec H e
  rw [h]
  simp [torusMap, Category.assoc]

end FLT.Mazur.ToricFiniteSubgroupRootsClassification
