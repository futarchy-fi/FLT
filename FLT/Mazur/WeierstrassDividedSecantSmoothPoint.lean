/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedSecantPoint

/-!
# Opposite-branch secants lie in the actual multiplication domain

Combine the two proved smooth inputs with the proved original smooth output.
This constructs a field point of the actual open on which the resolved
secant addition was defined, with both input and output maps preserved.
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

variable (hs : algebraMap R K (π ^ (start + j)) = 0)
  (h2 : algebraMap R K W.a₂ = 0) (ht : algebraMap R K W.a₁ ≠ 0)
  (hax : a (x W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) ≠ 0)
  (hcx : c (x W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) ≠ 0)
  (hay : a (y W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) = 0)
  (hcy : c (y W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6) =
    -algebraMap R K W.a₁ * c (x W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6))
local notation "p" => finiteDividedSecantPoint hπ data j hj a c ha hc hu
local notation "V" => finiteResolvedSecantOutputOpen hπ data j hj

include hs h2 ht hax hcx hay hcy in
/-- Opposite-branch residue equations put the actual source point in the actual output open. -/
theorem finiteDividedSecantPoint_range_outputOpen : Set.range p ⊆ V := by
  have ho : Set.range (p ≫ finiteResolvedSecantOriginalOutput hπ data j hj) ⊆
      WeierstrassIntegralChart.integralSmoothOpen W := by
    rw [finiteDividedSecantPoint_output]
    exact dividedSecantPoint_output_range_smooth W s (d).b3 (d).b4 (d).b6 a c hu
      (d).factor3 (d).factor4 (d).factor6 hs h2 ht hax hcx hay hcy
  rintro _ ⟨z, rfl⟩
  exact ho ⟨z, rfl⟩

/-- The actual opposite-branch point in the new resolved multiplication domain. -/
def finiteDividedSecantSmoothPoint : Spec (.of K) ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι p (by
    rw [Scheme.Opens.range_ι]
    exact finiteDividedSecantPoint_range_outputOpen hπ data j hj a c ha hc hu
      hs h2 ht hax hcx hay hcy)

/-- The new-domain point is exactly the constructed secant source point. -/
@[reassoc] theorem finiteDividedSecantSmoothPoint_inclusion :
    finiteDividedSecantSmoothPoint hπ data j hj a c ha hc hu hs h2 ht hax hcx hay hcy ≫
        (V).ι = p := IsOpenImmersion.lift_fac _ _ _

/-- Its two inputs are the original full resolved smooth pair. -/
@[reassoc] theorem finiteDividedSecantSmoothPoint_input :
    finiteDividedSecantSmoothPoint hπ data j hj a c ha hc hu hs h2 ht hax hcx hay hcy ≫
        finiteResolvedSecantDomainMap hπ data j hj =
      finiteDividedSmoothPair hπ data j hj a c ha hc := by
  rw [finiteResolvedSecantDomainMap, finiteDividedSecantSmoothPoint_inclusion_assoc,
    finiteDividedSecantPoint_input]

/-- Its resolved addition contracts to exactly the original universal secant output. -/
@[reassoc] theorem finiteDividedSecantSmoothPoint_addition :
    finiteDividedSecantSmoothPoint hπ data j hj a c ha hc hu hs h2 ht hax hcx hay hcy ≫
        finiteResolvedSecantAddition hπ data j hj ≫ (U).ι ≫
          finiteGlobalContraction hπ data j hj =
      f ≫ dividedSecantToCurve W s (d).b3 (d).b4 (d).b6
        (dividedPairLeft W s (d).b3 (d).b4 (d).b6)
        (dividedPairRight W s (d).b3 (d).b4 (d).b6) (d).factor3 (d).factor4 (d).factor6 := by
  rw [finiteResolvedSecantAddition_contraction,
    finiteDividedSecantSmoothPoint_inclusion_assoc, finiteDividedSecantPoint_output]

end FLT.Mazur.WeierstrassDividedDepth
