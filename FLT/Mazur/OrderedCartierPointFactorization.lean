/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCartierPointFactorization
public import FLT.Mazur.OrderedCurveDivisorPullback

/-!
# Ordered rational points representing the full Cartier ideal

Enumerating each support point as many times as its exponent converts the
point-power factorization to an ordered tuple. Repeated points encode the
original multiplicities; the empty divisor gives the empty tuple.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  [QuasiCompact f] {I : X.IdealSheafData}

/-- Every full Cartier ideal on the curve is an ordered product of rational point ideals. -/
theorem exists_orderedCartier_point_factorization (hI : EffectiveCartier I) :
    ∃ (d : ℕ) (p : Fin d → (Spec (.of k) ⟶ X)),
      (∀ i, p i ≫ f = 𝟙 _) ∧ I = ∏ i, (p i).ker := by
  classical
  obtain ⟨s, p, n, _, hp, _, _, hI⟩ := exists_finiteCartier_point_factorization f hI
  let α := Σ x : s, Fin (n x)
  let e := (Fintype.equivFin α).symm
  refine ⟨Fintype.card α, fun i ↦ p (e i).1, fun i ↦ hp _, ?_⟩
  calc
    I = ∏ x, (p x).ker ^ n x := hI
    _ = ∏ x : α, (p x.1).ker := by simp [α, Fintype.prod_sigma]
    _ = ∏ i, (p (e i).1).ker := (e.prod_comp (fun x : α ↦ (p x.1).ker)).symm

/-- The ordered tuple is an actual rational point of the fixed curve power. -/
theorem exists_orderedCartier_parameter (hI : EffectiveCartier I) :
    ∃ (d : ℕ) (a : Spec (.of k) ⟶ OrderedCurvePower.space f d),
      a ≫ OrderedCurvePower.base f d = 𝟙 _ ∧
      I = ∏ i, (a ≫ OrderedCurvePower.point f d i).ker := by
  obtain ⟨d, p, hp, hI⟩ := exists_orderedCartier_point_factorization f hI
  refine ⟨d, OrderedCurvePower.classify f d (𝟙 _) p hp,
    OrderedCurvePower.classify_base _ _ _ _ _, ?_⟩
  simpa only [OrderedCurvePower.classify_point] using hI

end FLT.Mazur.FCurve
