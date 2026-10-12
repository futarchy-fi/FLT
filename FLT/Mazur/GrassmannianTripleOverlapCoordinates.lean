/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapRing
public import FLT.Mazur.GrassmannianAmbientTransitionNaturality
public import FLT.Mazur.GrassmannianAmbientTransitionCocycle

/-!
# Universal coordinates on the triple intersection

The constructed triple-overlap ring carries the first and second quotient
coordinates. Their determinant conditions construct the composite overlap map,
and the universal rational coordinates satisfy the cocycle there.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ ν : Type*}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- The actual ambient transition specializes to its rational coordinate formula. -/
theorem ambientTransitionPolynomialHom_specialize
    {S : Type*} [CommRing S] [Algebra R S] (a : ambientOverlapRing e →ₐ[R] S) :
    matrixPolynomialHomEquiv R S κ d (a.comp (ambientTransitionPolynomialHom e)) =
      ambientTransitionMatrix ((ambientOverlapMatrix e).map a) (ambientEquivBaseChange S e) := by
  calc
    _ = (matrixPolynomialHomEquiv R (ambientOverlapRing e) κ d
        (ambientTransitionPolynomialHom e)).map a := by ext i j; rfl
    _ = _ := by
      rw [ambientTransitionPolynomialHom_matrix,
        ambientTransitionMatrix_algHom _ _ _ (ambientOverlapMatrix_isUnit e)]

variable (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The original quotient matrix on the triple intersection. -/
abbrev tripleOverlapMatrix := (ambientOverlapMatrix e).map (tripleOverlapFirstHom e f)

omit [Fintype ν] in
/-- The first overlap condition holds on the triple intersection. -/
theorem tripleOverlapMatrix_isUnit :
    IsUnit (ambientBasisMatrix (tripleOverlapMatrix e f)
      (ambientEquivBaseChange (tripleOverlapRing e f) e)).det :=
  ambientBasisMatrix_isUnit_algHom _ _ _ (ambientOverlapMatrix_isUnit e)

omit [Fintype ν] in
/-- The second overlap coordinates are the actual transition of the first coordinates. -/
theorem tripleOverlapNextHom_transition :
    (ambientOverlapMatrix f).map (tripleOverlapNextHom e f) =
      ambientTransitionMatrix (tripleOverlapMatrix e f)
        (ambientEquivBaseChange (tripleOverlapRing e f) e) := by
  rw [tripleOverlapNextHom_matrix, ambientTransitionPolynomialHom_matrix,
    ambientTransitionMatrix_algHom _ _ _ (ambientOverlapMatrix_isUnit e)]

/-- The second successive overlap condition holds on the triple intersection. -/
theorem tripleOverlapNextMatrix_isUnit :
    IsUnit (ambientBasisMatrix
      (ambientTransitionMatrix (tripleOverlapMatrix e f)
        (ambientEquivBaseChange (tripleOverlapRing e f) e))
      (ambientEquivBaseChange (tripleOverlapRing e f) f)).det := by
  rw [← tripleOverlapNextHom_transition]
  exact ambientBasisMatrix_isUnit_algHom _ _ _ (ambientOverlapMatrix_isUnit f)

/-- The composite overlap condition is constructed on the triple intersection. -/
theorem tripleOverlapCompositeMatrix_isUnit :
    IsUnit (ambientBasisMatrix (tripleOverlapMatrix e f)
      (ambientEquivBaseChange (tripleOverlapRing e f) (f.trans e))).det := by
  rw [ambientEquivBaseChange_trans]
  exact ambientBasisMatrix_comp_isUnit _ _ _
    (tripleOverlapMatrix_isUnit e f) (tripleOverlapNextMatrix_isUnit e f)

/-- The first polynomial chart restricts to the triple intersection. -/
def tripleOverlapOriginalPolynomialHom :
    MvPolynomial (Fin d × ι) R →ₐ[R] tripleOverlapRing e f :=
  (tripleOverlapFirstHom e f).comp (Algebra.algHom R _ _)

omit [Fintype ν] in
/-- The composite defining determinant is a unit under the original-chart map. -/
theorem tripleOverlapOriginalPolynomialHom_isUnit [Finite ν] :
    IsUnit (tripleOverlapOriginalPolynomialHom e f
      (overlapPolynomial (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap))) := by
  let _ := Fintype.ofFinite ν
  rw [overlapPolynomial_specialize]
  have hm : matrixPolynomialHomEquiv R (tripleOverlapRing e f) ι d
      (tripleOverlapOriginalPolynomialHom e f) = tripleOverlapMatrix e f := by
    ext i j
    rfl
  rw [hm]
  simpa only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange] using
    tripleOverlapCompositeMatrix_isUnit e f

/-- The actual map from the composite overlap ring to the triple intersection. -/
def tripleOverlapCompositeHom : ambientOverlapRing (f.trans e) →ₐ[R] tripleOverlapRing e f :=
  IsLocalization.Away.liftAlgHom
    (overlapPolynomial (ambientBlockP (f.trans e).toLinearMap)
      (ambientBlockQ (f.trans e).toLinearMap))
    (tripleOverlapOriginalPolynomialHom_isUnit e f)

/-- The composite-overlap map recovers the original polynomial coordinates. -/
theorem tripleOverlapCompositeHom_algebraMap (x : MvPolynomial (Fin d × ι) R) :
    tripleOverlapCompositeHom e f (algebraMap _ (ambientOverlapRing (f.trans e)) x) =
      tripleOverlapOriginalPolynomialHom e f x :=
  IsLocalization.Away.lift_eq _ (tripleOverlapOriginalPolynomialHom_isUnit e f) x

/-- The composite-overlap coordinates are the first coordinates on the triple intersection. -/
theorem tripleOverlapCompositeHom_matrix :
    (ambientOverlapMatrix (f.trans e)).map (tripleOverlapCompositeHom e f) =
      tripleOverlapMatrix e f := by
  ext i j
  exact tripleOverlapCompositeHom_algebraMap e f (MvPolynomial.X (i, j))

/-- The two actual third-chart classifying maps agree on the constructed triple intersection. -/
theorem tripleOverlapPolynomial_cocycle :
    (tripleOverlapCompositeHom e f).comp (ambientTransitionPolynomialHom (f.trans e)) =
      (tripleOverlapNextHom e f).comp (ambientTransitionPolynomialHom f) := by
  apply (matrixPolynomialHomEquiv R (tripleOverlapRing e f) ν d).injective
  rw [ambientTransitionPolynomialHom_specialize,
    ambientTransitionPolynomialHom_specialize, tripleOverlapCompositeHom_matrix,
    tripleOverlapNextHom_transition, ambientEquivBaseChange_trans]
  exact ambientTransitionMatrix_cocycle _ _ _
    (tripleOverlapMatrix_isUnit e f) (tripleOverlapNextMatrix_isUnit e f)

end FLT.Mazur.GrassmannianChart
