/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleSections

/-!
# Seven points and four laws on the true infinity triple intersection

Indices 0, 1, 2 denote the original inputs; 3, 4 the two inner sums; and 5, 6
the two final sums. Laws 0, 1, 2, 3 are respectively the first, last, left and
right additions. Every map is a restriction of the genuine full-cover member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The four genuine laws, in first/last/left/right order. -/
def infinityTripleScalarLaw (j : Fin 4) :
    InfinityAdditionOpen W →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  ![infinityTripleFullFirstAlg W hΔ, infinityTripleFullLastAlg W hΔ,
    infinityTripleFullLeftAlg W hΔ, infinityTripleFullRightAlg W hΔ] j

/-- All seven actual chart maps needed for associativity. -/
def infinityTripleScalarPoint (i : Fin 7) :
    Coordinate W 1 →ₐ[R] Γ(InfinityTripleFull W hΔ, ⊤) :=
  ![(infinityTripleFullFirstAlg W hΔ).comp (infinityInputLeft W),
    (infinityTripleFullFirstAlg W hΔ).comp (infinityInputRight W),
    (infinityTripleFullLastAlg W hΔ).comp (infinityInputRight W),
    (infinityTripleFullFirstAlg W hΔ).comp (infinityAdditionChart W),
    (infinityTripleFullLastAlg W hΔ).comp (infinityAdditionChart W),
    (infinityTripleFullLeftAlg W hΔ).comp (infinityAdditionChart W),
    (infinityTripleFullRightAlg W hΔ).comp (infinityAdditionChart W)] i

/-- Indices of the four left inputs. -/
def infinityTripleLeftIndex : Fin 4 → Fin 7 := ![0, 1, 3, 0]

/-- Indices of the four right inputs. -/
def infinityTripleRightIndex : Fin 4 → Fin 7 := ![1, 2, 2, 4]

/-- Indices of the four outputs. -/
def infinityTripleOutputIndex : Fin 4 → Fin 7 := ![3, 4, 5, 6]

/-- The indexed left input equations are consequences of the true triple projections. -/
theorem infinityTripleScalarLaw_left (j : Fin 4) :
    (infinityTripleScalarLaw W hΔ j).comp (infinityInputLeft W) =
      infinityTripleScalarPoint W hΔ (infinityTripleLeftIndex j) := by
  fin_cases j
  · rfl
  · exact (infinityTripleFullAlg_middle W hΔ).symm
  · exact infinityTripleFullAlg_left W hΔ
  · exact infinityTripleFullAlg_first W hΔ

/-- The indexed right input equations retain both genuine intermediate sums. -/
theorem infinityTripleScalarLaw_right (j : Fin 4) :
    (infinityTripleScalarLaw W hΔ j).comp (infinityInputRight W) =
      infinityTripleScalarPoint W hΔ (infinityTripleRightIndex j) := by
  fin_cases j
  · rfl
  · rfl
  · exact infinityTripleFullAlg_third W hΔ
  · exact infinityTripleFullAlg_right W hΔ

/-- Every indexed output is the original normalized addition map. -/
theorem infinityTripleScalarLaw_output (j : Fin 4) :
    (infinityTripleScalarLaw W hΔ j).comp (infinityAdditionChart W) =
      infinityTripleScalarPoint W hΔ (infinityTripleOutputIndex j) := by
  fin_cases j <;> rfl

/-- The actual normalized X coordinate of any of the seven points. -/
def infinityTripleScalarX (i : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarPoint W hΔ i (coord W 1 0)

/-- The actual normalized Z coordinate of any of the seven points. -/
def infinityTripleScalarZ (i : Fin 7) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarPoint W hΔ i (coord W 1 2)

/-- The regular slope of any of the four actual addition laws. -/
def infinityTripleScalarSlope (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarLaw W hΔ j (infinityChartSlope W)

/-- The actual output normalizer, not the leading coefficient of the line cubic. -/
def infinityTripleScalarScale (j : Fin 4) : Γ(InfinityTripleFull W hΔ, ⊤) :=
  infinityTripleScalarLaw W hΔ j
    (infinityOutputRestriction W (infinityOutputCoordinates W 1))

end FLT.Mazur.WeierstrassIntegralChart
