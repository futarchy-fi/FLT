/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialSchemeClassification

/-!
# Naturality of polynomial Hilbert representation over schemes

Arbitrary scheme base change pulls back the full ideal family and composes
its parameter morphism. The representing equivalence and its inverse
commute with these operations, with finite locally free degree derived from
the actual cartesian closed-family square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Arbitrary scheme base change of an actual finite locally free polynomial ideal family. -/
def polynomialSchemeFamilyBaseChange (J : PolynomialSchemeFamilies R I d s) :
    PolynomialSchemeFamilies R I d t :=
  ⟨J.val.comap (polynomialRelativeAmbientMap R I s t g hg),
    ClosedIdealCover.restriction_degree J.val _
      (polynomialRelativeAmbientMap_isPullback R I s t g hg) d J.property⟩

/-- Base change of a scheme parameter is the actual composite morphism over the coefficient base. -/
def polynomialSchemeParameterBaseChange (f : PolynomialSchemeParameters R I d s) :
    PolynomialSchemeParameters R I d t :=
  ⟨g ≫ f.val, by rw [Category.assoc, f.property, hg]⟩

/-- The representing equivalence commutes with every scheme base change. -/
theorem polynomialSchemeClassification_natural (f : PolynomialSchemeParameters R I d s) :
    polynomialSchemeClassification R I d t
        (polynomialSchemeParameterBaseChange R I d s t g hg f) =
      polynomialSchemeFamilyBaseChange R I d s t g hg
        (polynomialSchemeClassification R I d s f) := by
  apply Subtype.ext
  exact (polynomialSchemeParameterIdeal_baseChange R I d s f.val f.property t g hg).symm

/-- Actual classifying morphisms commute with arbitrary scheme base change. -/
theorem polynomialSchemeClassification_symm_natural (J : PolynomialSchemeFamilies R I d s) :
    (polynomialSchemeClassification R I d t).symm
        (polynomialSchemeFamilyBaseChange R I d s t g hg J) =
      polynomialSchemeParameterBaseChange R I d s t g hg
        ((polynomialSchemeClassification R I d s).symm J) := by
  apply (polynomialSchemeClassification R I d t).injective
  rw [Equiv.apply_symm_apply, polynomialSchemeClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
