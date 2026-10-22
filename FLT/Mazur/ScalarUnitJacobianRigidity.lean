/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraGeneratorDifferentials
public import FLT.Mazur.ScalarDifferentialJacobianAnnihilator

/-!
# Rigidity from a unit Jacobian in the full algebra

Coordinates can be arbitrary elements of the algebra, in particular arbitrary
fractions in a source stalk. The adjugate kills their differentials, and their
span kills the entire module without a reducedness or finiteness hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarUnitJacobianRigidity
open MvPolynomial ScalarDifferentialJacobianAnnihilator
variable {R L ι : Type} [CommRing R] [CommRing L] [Algebra R L]
  [Fintype ι] [DecidableEq ι]

/-- Coupled equations with a unit determinant kill all differential directions they span. -/
theorem formallyUnramified (z : ι → L) (F : ι → MvPolynomial ι R)
    (hz : Submodule.span L (Set.range fun i ↦ KaehlerDifferential.D R L (z i)) = ⊤)
    (hF : ∀ i, aeval z (F i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j ↦ aeval z (pderiv j (F i))))) :
    Algebra.FormallyUnramified R L := by
  have hd (i : ι) : KaehlerDifferential.D R L (z i) = 0 := by
    apply hJ.smul_eq_zero.mp
    apply det_smul_eq_zero _ (fun j ↦ KaehlerDifferential.D R L (z j)) _ i
    intro j
    rw [← map_aeval_sum, hF, map_zero]
  have h1 : (1 : L) ∈ Module.annihilator L (KaehlerDifferential R L) := by
    apply ScalarFiniteDifferentialGenerators.mem_annihilator z hz
    intro i
    simpa only [one_smul] using hd i
  exact (Algebra.formallyUnramified_iff R L).mpr
    (Module.annihilator_eq_top_iff.mp ((Ideal.eq_top_iff_one _).mpr h1))

/-- A presentation supplies spanning; no independent differential condition is needed. -/
theorem of_generators (z : ι → L) (F : ι → MvPolynomial ι R)
    (hz : Algebra.adjoin R (Set.range z) = ⊤) (hF : ∀ i, aeval z (F i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j ↦ aeval z (pderiv j (F i))))) :
    Algebra.FormallyUnramified R L :=
  formallyUnramified z F (ScalarAlgebraGeneratorDifferentials.span_eq_top z hz) hF hJ

end FLT.Mazur.ScalarUnitJacobianRigidity
