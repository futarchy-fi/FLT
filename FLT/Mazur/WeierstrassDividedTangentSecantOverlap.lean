/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSecantScheme
public import FLT.Mazur.WeierstrassDividedTangentOverlapProjections
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# The actual resolved tangent and secant lifts agree on their overlap

Equality of maps into the full resolved product retains both divided inputs.
The formulas agree before resolution; originally smooth output uniqueness
then identifies their actual lifts into the same finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "U" => (finiteGlobalStructure hπ data j hj).smoothLocus
local notation "Vt" => finiteResolvedTangentOutputOpen hπ data j hj
local notation "Vs" => finiteResolvedSecantOutputOpen hπ data j hj

variable {X : Scheme.{u}}
  (p : X ⟶ (finiteResolvedTangentOutputOpen hπ data j hj).toScheme)
  (q : X ⟶ (finiteResolvedSecantOutputOpen hπ data j hj).toScheme)
  (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj =
    q ≫ finiteResolvedSecantDomainMap hπ data j hj)

include hpq in
/-- The original formulas agree on the actual overlap inside the full resolved product. -/
theorem finiteResolvedTangent_secantOriginal :
    p ≫ (Vt).ι ≫ finiteResolvedTangentOriginalOutput hπ data j hj =
      q ≫ (Vs).ι ≫ finiteResolvedSecantOriginalOutput hπ data j hj := by
  have ht : finiteResolvedTangentProjection hπ data j hj ≫ finiteTangentInput hπ data j hj =
      finiteResolvedTangentDomainMap hπ data j hj ≫
        finiteResolvedPairInclusion hπ data j hj := by
    simp only [finiteResolvedTangentProjection, finiteResolvedTangentDomainMap,
      finiteResolvedTangentInput, Category.assoc, pullback.condition]
  have hs : finiteResolvedSecantProjection hπ data j hj ≫ finiteSecantInput hπ data j hj =
      finiteResolvedSecantDomainMap hπ data j hj ≫
        finiteResolvedPairInclusion hπ data j hj := by
    simp only [finiteResolvedSecantProjection, finiteResolvedSecantDomainMap,
      finiteResolvedSecantInput, Category.assoc, pullback.condition]
  have he : (p ≫ finiteResolvedTangentProjection hπ data j hj) ≫
      dividedPairTangentInclusion W s (d).b3 (d).b4 (d).b6 =
        (q ≫ finiteResolvedSecantProjection hπ data j hj) ≫
          dividedPairSecantInclusion W s (d).b3 (d).b4 (d).b6 := by
    apply (cancel_mono (dividedPairSpecIso W s (d).b3 (d).b4 (d).b6).inv).mp
    apply (cancel_mono (finiteSecantPairChart hπ data j hj)).mp
    have h := congrArg (· ≫ finiteResolvedPairInclusion hπ data j hj) hpq
    rw [Category.assoc, Category.assoc, ← ht, ← hs] at h
    simpa only [finiteTangentInput, finiteSecantInput, dividedPairTangentToProduct,
      dividedPairSecantToProduct, Category.assoc] using h
  have h := dividedTangentSecant_scheme W s (d).b3 (d).b4 (d).b6 a c
    (d).factor3 (d).factor4 (d).factor6
    (p ≫ finiteResolvedTangentProjection hπ data j hj)
    (q ≫ finiteResolvedSecantProjection hπ data j hj) he
  simpa only [Category.assoc, finiteResolvedTangentProjection_output,
    finiteResolvedSecantProjection_output] using h

include hpq in
/-- Equality of actual resolved lifts uses only uniqueness above an originally smooth output. -/
theorem finiteResolvedTangent_secantOverlap :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ finiteResolvedSecantAddition hπ data j hj := by
  apply (cancel_mono (U).ι).mp
  apply finiteGlobal_smooth_output_hom_ext hπ data j hj
    (p ≫ finiteResolvedTangentOriginalSmooth hπ data j hj)
  · simp only [Category.assoc, finiteResolvedTangentAddition_contraction,
      finiteResolvedTangentOriginalSmooth_inclusion]
  · simp only [Category.assoc, finiteResolvedSecantAddition_contraction,
      finiteResolvedTangentOriginalSmooth_inclusion]
    exact (finiteResolvedTangent_secantOriginal hπ data j hj p q hpq).symm

end FLT.Mazur.WeierstrassDividedDepth
