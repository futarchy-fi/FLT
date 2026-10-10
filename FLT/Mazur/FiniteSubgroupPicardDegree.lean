/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupPicard
public import FLT.Mazur.FiniteFieldRankLength
public import FLT.Mazur.FiniteDivisorCohomology
public import FLT.Mazur.CurvePicardDegree

/-!
# The cohomological degree of a finite subgroup divisor

The scheme-theoretic rank of the actual finite subgroup computes its closed
divisor length, hence the degree of its positive divisor line bundle. This
also computes every field-valued fiber of a relative Cartier subgroup.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

open FCurve

variable {K : Type} [Field K] {E : GeneralizedEllipticCurve (Spec (.of K))}
  {n : ℕ} (H : E.FiniteSubgroup n)

/-- The actual closed subgroup divisor has length its prescribed finite-flat rank. -/
theorem divisorFieldLength_eq_rank : divisorFieldLength E.curve.hom H.ideal = n := by
  have : IsFinite (H.ideal.subschemeι ≫ E.curve.hom) := H.ideal_degree.1
  exact (finrank_eq_finiteSchemeLength (H.ideal.subschemeι ≫ E.curve.hom)
    (IsLocalRing.closedPoint K)).symm.trans (H.ideal_degree.2.2.2 _)

/-- The positive subgroup divisor class has cohomological degree equal to its rank. -/
theorem divisorPicardClass_degree (hI : EffectiveCartier H.ideal) :
    SchemePicard.degree E.curve.hom (H.divisorPicardClass hI) = (n : ℤ) := by
  have : IsProper E.curve.hom := E.family.family.1
  have : IsFinite (H.ideal.subschemeι ≫ E.curve.hom) := H.ideal_degree.1
  change curveSheafDegree E.curve.hom (divisorLineBundle H.ideal hI) = _
  rw [divisor_degree_eq_fieldLength, H.divisorFieldLength_eq_rank]

/-- Every field-valued fiber of a Cartier subgroup has the original rank as degree. -/
theorem divisorPicardClass_fiber_degree {S : Scheme} {F : GeneralizedEllipticCurve S}
    (J : F.FiniteSubgroup n) (hJ : EffectiveCartier J.ideal) (g : Spec (.of K) ⟶ S) :
    SchemePicard.degree (F.baseChange g).curve.hom
      (SchemePicard.pullback (pullback.fst F.curve.hom g) (J.divisorPicardClass hJ)) =
        (n : ℤ) := by
  rw [← J.divisorPicardClass_baseChange hJ g]
  exact (J.baseChange g).divisorPicardClass_degree _

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
