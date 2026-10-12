/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementExhaustion
public import FLT.Mazur.FilteredPoleInfiniteIndependence
public import FLT.Mazur.GenusOneGroupWeierstrassEquation
public import FLT.Mazur.WeierstrassAffineEvaluationRange

/-!
# The coordinate ring of the original geometric group's point complement

The constructed normalized coordinates are independent by their exact poles.
Monomial bases and pole exhaustion show that they generate all regular functions.
Thus their actual Weierstrass coordinate evaluation is a ring isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- Use the actual complement section ring on its bundled field module. -/
local instance coordinateFunctionRing : CommRing (divisorComplementModule G.hom s.left.ker) :=
  inferInstanceAs (CommRing
    Γ((Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl), ⊤))

local notation "x" => genusOneGroupPoleFunction G hd hc hg s hI 1 (by decide)
local notation "y" => genusOneGroupPoleFunction G hd hc hg s hI 2 (by decide)
local notation "P" => divisorPoleSubmodule G.hom hI
local notation "A" => divisorComplementModule G.hom s.left.ker

/-- Evaluate the constructed equation in the normalized original functions. -/
def coordinateEvaluation : (equation G hd hc hg s hI).toAffine.CoordinateRing →+* A :=
  WeierstrassAffineEquationEvaluation.evaluation _ (scalar G s)
    (normalize G hd hc hg s hI x) (normalize G hd hc hg s hI y)
    (equation_holds G hd hc hg s hI)

/-- The entire ordered family of original monomials is independent. -/
theorem monomial_linearIndependent : LinearIndependent k (monomial G hd hc hg s hI) :=
  FilteredPoleBasis.linearIndependent_of_nat_orders P (divisorPoleSubmodule_mono G.hom hI)
    _ _ WeightedPoleMonomials.order_strictMono (monomial_mem G hd hc hg s hI)
    (monomial_ne_zero G hd hc hg s hI) (monomial_not_mem_lt G hd hc hg s hI)

/-- The actual normalized coordinate evaluation is injective. -/
theorem coordinateEvaluation_injective :
    Function.Injective (coordinateEvaluation G hd hc hg s hI) := by
  apply WeierstrassAffineEquationEvaluation.evaluation_injective
  apply WeightedPoleMonomials.linearIndependent_normal
  exact WeightedPoleMonomials.linearIndependent_scaled (scalar G s) x y _
    (cubicCoefficients_last_ne_zero G hd hc hg s hI)
    (monomial_linearIndependent G hd hc hg s hI)

/-- The same evaluation with the original bundled field-linear target. -/
def coordinateLinear : (equation G hd hc hg s hI).toAffine.CoordinateRing →ₗ[k] A :=
  WeierstrassAffineEquationEvaluation.evaluationLinear _ (scalar G s)
    (normalize G hd hc hg s hI x) (normalize G hd hc hg s hI y)
    (equation_holds G hd hc hg s hI)

/-- Undoing the nonzero scale recovers each original monomial in the coordinate image. -/
theorem monomial_mem_range (j : ℕ) :
    monomial G hd hc hg s hI j ∈ (coordinateLinear G hd hc hg s hI).range :=
  WeierstrassAffineEquationEvaluation.originalMonomial_mem_evaluation_range _ _ _ _ _
    (cubicCoefficients_last_ne_zero G hd hc hg s hI) (equation_holds G hd hc hg s hI) j

/-- Every bounded original pole function belongs to the coordinate image. -/
theorem pole_le_coordinateRange (m : ℕ) : P m ≤ (coordinateLinear G hd hc hg s hI).range := by
  intro z hz
  have hz' := divisorPoleSubmodule_mono G.hom hI (Nat.le_succ m) hz
  have he := FilteredPoleBasis.sum_repr_coe P
    (monomialBasis G hd hc hg s hI (m + 1)) ⟨z, hz'⟩
  change _ = z at he
  rw [← he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [monomialBasis_apply]
  exact monomial_mem_range G hd hc hg s hI j

/-- Pole exhaustion makes evaluation surjective onto the actual complement functions. -/
theorem coordinateEvaluation_surjective :
    Function.Surjective (coordinateEvaluation G hd hc hg s hI) := by
  let _ := Chow.source_isNoetherian G.hom
  intro z
  obtain ⟨m, hm⟩ := exists_mem_divisorPoleSubmodule hI G.hom z
  exact pole_le_coordinateRange G hd hc hg s hI m hm

/-- The original complement function ring is the constructed Weierstrass coordinate ring. -/
def coordinateRingEquiv : (equation G hd hc hg s hI).toAffine.CoordinateRing ≃+* A :=
  RingEquiv.ofBijective (coordinateEvaluation G hd hc hg s hI)
    ⟨coordinateEvaluation_injective G hd hc hg s hI,
      coordinateEvaluation_surjective G hd hc hg s hI⟩

/-- The isomorphism retains exactly the original field scalar map. -/
theorem coordinateRingEquiv_scalars (a : k) :
    coordinateRingEquiv G hd hc hg s hI
      (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing a) = scalar G s a :=
  WeierstrassAffineEquationEvaluation.evaluation_scalar (equation G hd hc hg s hI)
    (scalar G s) _ _ (equation_holds G hd hc hg s hI) a

end FLT.Mazur.GenusOneGroupCoordinates
