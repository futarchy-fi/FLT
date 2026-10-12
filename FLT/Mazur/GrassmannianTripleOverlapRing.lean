/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedAmbientTransition

/-!
# The actual successive triple-overlap coordinate ring

Inside the first determinant overlap, invert the third-basis determinant pulled
back from the second chart. The resulting localization has constructed maps from
both successive overlap rings and represents precisely this additional open condition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ ν : Type*}
  [Fintype ι] [Fintype κ] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The next-basis determinant pulled back to the first determinant overlap. -/
def tripleOverlapElement : ambientOverlapRing e :=
  ambientTransitionPolynomialHom e
    (overlapPolynomial (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap))

/-- The coordinate ring of the successive triple intersection. -/
abbrev tripleOverlapRing := Localization.Away (tripleOverlapElement e f)

/-- The first overlap restricts to the actual triple intersection. -/
def tripleOverlapFirstHom : ambientOverlapRing e →ₐ[R] tripleOverlapRing e f :=
  Algebra.algHom R _ _

/-- The second chart coordinates restricted to the triple intersection. -/
def tripleOverlapSecondPolynomialHom :
    MvPolynomial (Fin d × κ) R →ₐ[R] tripleOverlapRing e f :=
  (tripleOverlapFirstHom e f).comp (ambientTransitionPolynomialHom e)

/-- The next determinant is a unit by construction of the triple intersection. -/
theorem tripleOverlapSecondPolynomialHom_isUnit :
    IsUnit (tripleOverlapSecondPolynomialHom e f
      (overlapPolynomial (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap))) :=
  IsLocalization.Away.algebraMap_isUnit (tripleOverlapElement e f)

/-- The triple intersection maps to the second successive determinant overlap. -/
def tripleOverlapNextHom : ambientOverlapRing f →ₐ[R] tripleOverlapRing e f :=
  IsLocalization.Away.liftAlgHom
    (overlapPolynomial (ambientBlockP f.toLinearMap) (ambientBlockQ f.toLinearMap))
    (tripleOverlapSecondPolynomialHom_isUnit e f)

/-- The second overlap map restricts to the specified second-chart coordinates. -/
theorem tripleOverlapNextHom_algebraMap (x : MvPolynomial (Fin d × κ) R) :
    tripleOverlapNextHom e f (algebraMap _ (ambientOverlapRing f) x) =
      tripleOverlapSecondPolynomialHom e f x :=
  IsLocalization.Away.lift_eq _ (tripleOverlapSecondPolynomialHom_isUnit e f) x

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The triple intersection represents maps to the first overlap with unit next determinant. -/
def tripleOverlapHomEquiv :
    (tripleOverlapRing e f →ₐ[R] S) ≃
      {a : ambientOverlapRing e →ₐ[R] S // IsUnit (a (tripleOverlapElement e f))} where
  toFun a := ⟨a.comp (tripleOverlapFirstHom e f),
    (IsLocalization.Away.algebraMap_isUnit (tripleOverlapElement e f)).map a⟩
  invFun a := IsLocalization.Away.liftAlgHom (tripleOverlapElement e f) a.property
  left_inv a := by
    apply IsLocalization.algHom_ext (Submonoid.powers (tripleOverlapElement e f))
    apply AlgHom.ext
    intro x
    simp [tripleOverlapFirstHom, Algebra.algHom, IsLocalization.Away.liftAlgHom]
  right_inv a := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    simp [tripleOverlapFirstHom, Algebra.algHom, IsLocalization.Away.liftAlgHom]

/-- The actual next overlap coordinates are the restricted first transition coordinates. -/
theorem tripleOverlapNextHom_matrix :
    (ambientOverlapMatrix f).map (tripleOverlapNextHom e f) =
      (matrixPolynomialHomEquiv R (ambientOverlapRing e) κ d
        (ambientTransitionPolynomialHom e)).map (tripleOverlapFirstHom e f) := by
  ext i j
  exact tripleOverlapNextHom_algebraMap e f (MvPolynomial.X (i, j))

end FLT.Mazur.GrassmannianChart
