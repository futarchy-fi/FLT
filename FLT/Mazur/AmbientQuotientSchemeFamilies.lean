/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientQuotientRelativeSpace
public import FLT.Mazur.ClosedImmersionIdealDegree
public import FLT.Mazur.HilbertPolynomialSchemeClassification

/-!
# All actual finite locally free families in an affine quotient ambient

Full ideals on the actual quotient ambient base change correspond exactly
to polynomial finite locally free families containing the full ambient
kernel. No local bases or chosen ambient factorization are supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- All actual full ideals of finite locally free degree in the quotient ambient base change. -/
def QuotientSchemeFamilies :=
  { J : (quotientRelativeAmbient R I K s).IdealSheafData //
    FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst _ _) d }

/-- All polynomial finite locally free families contained in the actual quotient ambient. -/
def ContainedPolynomialSchemeFamilies :=
  { J : PolynomialSchemeFamilies R I d s // (quotientRelativeImmersion R I K s).ker ≤ J.val }

/-- Pushing forward the actual quotient family retains its geometric finite locally free degree. -/
theorem quotientSchemeFamily_map_degree (J : QuotientSchemeFamilies R I d K s) :
    FiniteLocallyFreeDegree
      ((J.val.map (quotientRelativeImmersion R I K s)).subschemeι ≫ pullback.fst _ _) d := by
  apply (closedIdeal_degree_iff (quotientRelativeImmersion R I K s) (pullback.fst _ _) J.val d).mp
  rw [quotientRelativeImmersion_fst]
  exact J.property

/-- Restricting a containing polynomial family to the quotient ambient retains its degree. -/
theorem containedPolynomialSchemeFamily_comap_degree
    (J : ContainedPolynomialSchemeFamilies R I d K s) :
    FiniteLocallyFreeDegree
      ((J.val.val.comap (quotientRelativeImmersion R I K s)).subschemeι ≫ pullback.fst _ _) d := by
  have h := (closedIdeal_degree_iff (quotientRelativeImmersion R I K s) (pullback.fst _ _)
    (J.val.val.comap (quotientRelativeImmersion R I K s)) d).mpr (by
      rw [closed_map_comap _ _ J.property]
      exact J.val.property)
  rwa [quotientRelativeImmersion_fst] at h

/-- Actual quotient-ambient families correspond to all containing polynomial families. -/
def quotientSchemeFamilyCorrespondence :
    QuotientSchemeFamilies R I d K s ≃ ContainedPolynomialSchemeFamilies R I d K s where
  toFun J := ⟨⟨J.val.map (quotientRelativeImmersion R I K s),
    quotientSchemeFamily_map_degree R I d K s J⟩, Scheme.Hom.le_ker_comp _ _⟩
  invFun J := ⟨J.val.val.comap (quotientRelativeImmersion R I K s),
    containedPolynomialSchemeFamily_comap_degree R I d K s J⟩
  left_inv J := Subtype.ext (closed_comap_map _ J.val)
  right_inv J := Subtype.ext (Subtype.ext (closed_map_comap _ J.val.val J.property))

/-- The correspondence takes the full ideal of the composite actual closed immersion. -/
theorem quotientSchemeFamilyCorrespondence_ideal (J : QuotientSchemeFamilies R I d K s) :
    (quotientSchemeFamilyCorrespondence R I d K s J).val.val =
      (J.val.subschemeι ≫ quotientRelativeImmersion R I K s).ker := rfl

end FLT.Mazur.HilbertChart
