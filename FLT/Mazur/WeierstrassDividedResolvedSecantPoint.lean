/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSmoothInput
public import FLT.Mazur.WeierstrassDividedSecantPointGeometry

/-!
# Actual field-valued pairs in the resolved secant source

Two divided inputs with nonzero vertical derivatives and distinct divided
abscissae construct a point of the previously defined resolved secant source.
Both inputs range over the same entire finite model's smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [Field K] [Algebra R K] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W s (d).b3 (d).b4 (d).b6)))
variable (a c : Coordinate W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] K)
  (ha : a (verticalDerivative W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) ≠ 0)
  (hc : c (verticalDerivative W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) ≠ 0)
  (hu : IsUnit (a (x W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) -
    c (x W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6)))
local notation "e" => dividedPairSecantEvaluation W s (d).b3 (d).b4 (d).b6 a c hu
local notation "f" => Spec.map (CommRingCat.ofHom (e).toRingHom)

/-- Both actual divided inputs define a point of the full resolved smooth product. -/
def finiteDividedSmoothPair : Spec (.of K) ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.lift (finiteDividedSmoothInput hπ data j hj a ha)
    (finiteDividedSmoothInput hπ data j hj c hc) (by
      simp only [finiteDividedSmoothInput_structure])

/-- The universal secant factorization and the two smooth inputs define the same ambient pair. -/
theorem finiteDividedSmoothPair_secant :
    f ≫ finiteSecantInput hπ data j hj =
      finiteDividedSmoothPair hπ data j hj a c ha hc ≫
        finiteResolvedPairInclusion hπ data j hj := by
  apply pullback.hom_ext
  · simp only [finiteSecantInput, finiteSecantPairChart, finiteResolvedPairInclusion,
      pullback.map, Category.assoc, pullback.lift_fst_assoc, finiteDividedSmoothPair,
      pullback.lift_fst, finiteDividedSmoothInput_inclusion]
    exact dividedSecantPoint_fst_assoc W s (d).b3 (d).b4 (d).b6 a c hu _
  · simp only [finiteSecantInput, finiteSecantPairChart, finiteResolvedPairInclusion,
      pullback.map, Category.assoc, pullback.lift_snd_assoc, finiteDividedSmoothPair,
      pullback.lift_snd, finiteDividedSmoothInput_inclusion]
    exact dividedSecantPoint_snd_assoc W s (d).b3 (d).b4 (d).b6 a c hu _

/-- The actual pair factors through the constructed resolved secant source. -/
def finiteDividedSecantPoint : Spec (.of K) ⟶ finiteResolvedSecantSource hπ data j hj :=
  pullback.lift f (finiteDividedSmoothPair hπ data j hj a c ha hc)
    (finiteDividedSmoothPair_secant hπ data j hj a c ha hc hu)

/-- The factorization retains its exact universal secant point. -/
@[reassoc] theorem finiteDividedSecantPoint_fst :
    finiteDividedSecantPoint hπ data j hj a c ha hc hu ≫
        pullback.fst (finiteSecantInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj) =
      f := pullback.lift_fst _ _ _

/-- The same factorization retains both complete resolved smooth inputs. -/
@[reassoc] theorem finiteDividedSecantPoint_input :
    finiteDividedSecantPoint hπ data j hj a c ha hc hu ≫
        finiteResolvedSecantInput hπ data j hj =
      finiteDividedSmoothPair hπ data j hj a c ha hc := pullback.lift_snd _ _ _

/-- Its constructed original output is exactly the universal divided secant formula. -/
@[reassoc] theorem finiteDividedSecantPoint_output :
    finiteDividedSecantPoint hπ data j hj a c ha hc hu ≫
        finiteResolvedSecantOriginalOutput hπ data j hj =
      f ≫ dividedSecantToCurve W s (d).b3 (d).b4 (d).b6
        (dividedPairLeft W s (d).b3 (d).b4 (d).b6)
        (dividedPairRight W s (d).b3 (d).b4 (d).b6) (d).factor3 (d).factor4 (d).factor6 := by
  rw [finiteResolvedSecantOriginalOutput, finiteDividedSecantPoint_fst_assoc]

end FLT.Mazur.WeierstrassDividedDepth
