/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientBaseChange

/-!
# Four blocks of an ambient coordinate change

Every finite ambient linear map has four actual coefficient matrices. For a
scalar-extended equivalence these are the coefficientwise images of the base blocks.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- The selected-to-selected block of an ambient linear map. -/
def ambientBlockP
    (f : ((Fin d → R) × (κ → R)) →ₗ[R] ((Fin d → R) × (ι → R))) :
    Matrix (Fin d) (Fin d) R := by
  classical
  exact LinearMap.toMatrix' ((LinearMap.fst R _ _).comp
    (f.comp (LinearMap.inl R _ _)))

/-- The selected-to-complementary block of an ambient linear map. -/
def ambientBlockQ
    (f : ((Fin d → R) × (κ → R)) →ₗ[R] ((Fin d → R) × (ι → R))) :
    Matrix ι (Fin d) R := by
  classical
  exact LinearMap.toMatrix' ((LinearMap.snd R _ _).comp
    (f.comp (LinearMap.inl R _ _)))

/-- The complementary-to-selected block of an ambient linear map. -/
def ambientBlockU
    (f : ((Fin d → R) × (κ → R)) →ₗ[R] ((Fin d → R) × (ι → R))) :
    Matrix (Fin d) κ R := by
  classical
  exact LinearMap.toMatrix' ((LinearMap.fst R _ _).comp
    (f.comp (LinearMap.inr R _ _)))

/-- The complementary-to-complementary block of an ambient linear map. -/
def ambientBlockT
    (f : ((Fin d → R) × (κ → R)) →ₗ[R] ((Fin d → R) × (ι → R))) :
    Matrix ι κ R := by
  classical
  exact LinearMap.toMatrix' ((LinearMap.snd R _ _).comp
    (f.comp (LinearMap.inr R _ _)))

omit [Fintype ι] in
/-- The four constructed blocks recover the full ambient linear map. -/
theorem ambientBlocks_reconstruct
    (f : ((Fin d → R) × (κ → R)) →ₗ[R] ((Fin d → R) × (ι → R))) :
    blockAmbientMap (ambientBlockP f) (ambientBlockQ f) (ambientBlockU f)
      (ambientBlockT f) = f := by
  classical
  simp only [blockAmbientMap, matrixSelectedSummand, ambientBlockP, ambientBlockQ,
    ambientBlockU, ambientBlockT, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  change f (x.1, 0) + f (0, x.2) = f x
  rw [← map_add]
  simp

variable (S : Type*) [CommRing S] [Algebra R S]
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- Coordinatewise scalar extension carries coordinate basis vectors to basis vectors. -/
theorem scalarMap_single {α : Type*} [DecidableEq α] (j : α) :
    (fun i ↦ algebraMap R S ((Pi.single j (1 : R) : α → R) i)) = Pi.single j (1 : S) := by
  ext i
  simp [Pi.single_apply]

/-- Scalar extension maps the selected block coefficientwise. -/
theorem ambientBlockP_baseChange :
    ambientBlockP (ambientEquivBaseChange S e).toLinearMap =
      (ambientBlockP e.toLinearMap).map (algebraMap R S) := by
  classical
  ext i j
  have h := ambientEquivBaseChange_algebraMap S e (Pi.single j 1, 0)
  simpa [ambientBlockP, LinearMap.toMatrix'_apply, scalarMap_single, Pi.zero_def] using
    congrArg (fun x ↦ x.1 i) h

/-- Scalar extension maps the lower selected block coefficientwise. -/
theorem ambientBlockQ_baseChange :
    ambientBlockQ (ambientEquivBaseChange S e).toLinearMap =
      (ambientBlockQ e.toLinearMap).map (algebraMap R S) := by
  classical
  ext i j
  have h := ambientEquivBaseChange_algebraMap S e (Pi.single j 1, 0)
  simpa [ambientBlockQ, LinearMap.toMatrix'_apply, scalarMap_single, Pi.zero_def] using
    congrArg (fun x ↦ x.2 i) h

/-- Scalar extension maps the upper complementary block coefficientwise. -/
theorem ambientBlockU_baseChange :
    ambientBlockU (ambientEquivBaseChange S e).toLinearMap =
      (ambientBlockU e.toLinearMap).map (algebraMap R S) := by
  classical
  ext i j
  have h := ambientEquivBaseChange_algebraMap S e (0, Pi.single j 1)
  simpa [ambientBlockU, LinearMap.toMatrix'_apply, scalarMap_single, Pi.zero_def] using
    congrArg (fun x ↦ x.1 i) h

/-- Scalar extension maps the lower complementary block coefficientwise. -/
theorem ambientBlockT_baseChange :
    ambientBlockT (ambientEquivBaseChange S e).toLinearMap =
      (ambientBlockT e.toLinearMap).map (algebraMap R S) := by
  classical
  ext i j
  have h := ambientEquivBaseChange_algebraMap S e (0, Pi.single j 1)
  simpa [ambientBlockT, LinearMap.toMatrix'_apply, scalarMap_single, Pi.zero_def] using
    congrArg (fun x ↦ x.2 i) h

/-- The scalar-extended equivalence is exactly the ambient map of the specialized blocks. -/
theorem ambientEquivBaseChange_blocks :
    (ambientEquivBaseChange S e).toLinearMap =
      blockAmbientMap ((ambientBlockP e.toLinearMap).map (algebraMap R S))
        ((ambientBlockQ e.toLinearMap).map (algebraMap R S))
        ((ambientBlockU e.toLinearMap).map (algebraMap R S))
        ((ambientBlockT e.toLinearMap).map (algebraMap R S)) := by
  rw [← ambientBlockP_baseChange, ← ambientBlockQ_baseChange,
    ← ambientBlockU_baseChange, ← ambientBlockT_baseChange, ambientBlocks_reconstruct]

end FLT.Mazur.GrassmannianChart
