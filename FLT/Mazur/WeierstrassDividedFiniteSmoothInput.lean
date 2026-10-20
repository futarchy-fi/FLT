/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedOppositeInputs
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# Smooth divided inputs in the same entire finite model

A nonzero divided vertical derivative lifts the actual field-valued input
into the relative smooth locus of the entire finite model. The lift retains
both the original cubic contraction and the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
variable (a : Coordinate W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] K)
  (ha : a (verticalDerivative W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) ≠ 0)

include ha in
/-- The actual divided field point lands in the full finite model's relative smooth locus. -/
theorem finiteDividedFieldPoint_range_smooth :
    Set.range (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      finiteSecantDividedChart hπ data j hj) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at h
  exact h.ge (dividedFieldPoint_range_smooth W s (d).b3 (d).b4 (d).b6 a ha ⟨z, rfl⟩)

/-- Lift the input without changing the finite projective model or its coefficient point. -/
def finiteDividedSmoothInput : Spec (.of K) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι
    (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ finiteSecantDividedChart hπ data j hj)
    (by rw [Scheme.Opens.range_ι]; exact finiteDividedFieldPoint_range_smooth hπ data j hj a ha)

/-- The smooth input retains the actual original finite-model map. -/
@[reassoc] theorem finiteDividedSmoothInput_inclusion :
    finiteDividedSmoothInput hπ data j hj a ha ≫ (U).ι =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ finiteSecantDividedChart hπ data j hj :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its cubic contraction is precisely the original divided contraction. -/
@[reassoc] theorem finiteDividedSmoothInput_contraction :
    finiteDividedSmoothInput hπ data j hj a ha ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d := by
  rw [finiteDividedSmoothInput_inclusion_assoc,
    finiteSecantDividedChart_contraction]

/-- The lifted input lies over its unchanged coefficient field point. -/
@[reassoc] theorem finiteDividedSmoothInput_structure :
    finiteDividedSmoothInput hπ data j hj a ha ≫ (U).ι ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [finiteDividedSmoothInput_inclusion_assoc,
    finiteSecantDividedChart_structure]
  exact WeierstrassIntegralChart.specAlgHom_structure a

end FLT.Mazur.WeierstrassDividedDepth
