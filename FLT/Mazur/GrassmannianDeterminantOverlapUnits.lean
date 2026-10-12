/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapCoordinates

/-!
# Determinant units on the actual Grassmannian overlaps

The quotient basis determinant is a unit in the original overlap ring.
Its images multiply on the constructed triple intersection, giving the
multiplicative transition data for the determinant line.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ ν : Type*}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- The actual quotient-basis determinant, as a unit of the full overlap ring. -/
def determinantOverlapUnit : (ambientOverlapRing e)ˣ :=
  (ambientOverlapMatrix_isUnit e).unit

/-- The unit retains the original quotient-basis determinant. -/
theorem determinantOverlapUnit_val :
    (determinantOverlapUnit e : ambientOverlapRing e) =
      (ambientBasisMatrix (ambientOverlapMatrix e)
        (ambientEquivBaseChange (ambientOverlapRing e) e)).det :=
  (ambientOverlapMatrix_isUnit e).unit_spec

/-- The determinant unit specializes to the determinant over every coefficient algebra. -/
theorem determinantOverlapUnit_map_val {S : Type*} [CommRing S] [Algebra R S]
    (a : ambientOverlapRing e →ₐ[R] S) :
    a (determinantOverlapUnit e : ambientOverlapRing e) =
      (ambientBasisMatrix ((ambientOverlapMatrix e).map a)
        (ambientEquivBaseChange S e)).det := by
  rw [determinantOverlapUnit_val, AlgHom.map_det]
  congr 1
  exact ambientBasisMatrix_algHom a _ e

variable (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The determinant transition cocycle holds in the actual triple-localized ring. -/
theorem determinantOverlapUnit_cocycle :
    Units.map (tripleOverlapCompositeHom e f).toMonoidHom
        (determinantOverlapUnit (f.trans e)) =
      Units.map (tripleOverlapFirstHom e f).toMonoidHom (determinantOverlapUnit e) *
        Units.map (tripleOverlapNextHom e f).toMonoidHom (determinantOverlapUnit f) := by
  apply Units.ext
  change tripleOverlapCompositeHom e f (determinantOverlapUnit (f.trans e) : _) =
    tripleOverlapFirstHom e f (determinantOverlapUnit e : _) *
      tripleOverlapNextHom e f (determinantOverlapUnit f : _)
  rw [determinantOverlapUnit_map_val, determinantOverlapUnit_map_val,
    determinantOverlapUnit_map_val, tripleOverlapCompositeHom_matrix,
    tripleOverlapNextHom_transition, ambientEquivBaseChange_trans,
    ambientBasisMatrix_comp _ _ _ (tripleOverlapMatrix_isUnit e f), Matrix.det_mul]

end FLT.Mazur.GrassmannianChart
