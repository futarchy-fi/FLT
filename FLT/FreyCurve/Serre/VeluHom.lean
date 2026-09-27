/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAdditivity
public import FLT.FreyCurve.Serre.VeluOrdinary
public import FLT.FreyCurve.Serre.VeluPointCofinite

/-!
# Additivity of the Vélu point map

Specialization gives addition outside finitely many first summands. An auxiliary
summand then proves the addition law at every pair of points.
-/

@[expose] public section

namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (G : AddSubgroup E.toAffine.Point)

omit [CharZero K] [IsAlgClosed K] [E.IsElliptic] in
/-- A finite subgroup contains only finitely many points. -/
theorem eventually_not_mem_kernel [Finite G] : ∀ᶠ P in Filter.cofinite, P ∉ G := by
  exact Filter.eventually_cofinite.mpr (by simpa using (Set.toFinite (G : Set E.toAffine.Point)))

variable [Fintype G]

omit [IsAlgClosed K] in
/-- For each translating point, the Vélu addition law fails at most finitely often. -/
theorem pointMap_add_cofinite (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (h : ∀ P, P ∉ G → (curve E G).toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (Q : E.toAffine.Point) :
    ∀ᶠ P in Filter.cofinite,
      pointMap E G (curve E G) h (P + Q) =
        pointMap E G (curve E G) h P + pointMap E G (curve E G) h Q := by
  classical
  by_cases hQG : Q ∈ G
  · exact Filter.Eventually.of_forall fun P => pointMap_add_of_mem_right E G _ h P Q hQG
  cases Q with
  | zero => exact (hQG G.zero_mem).elim
  | some u v hQ =>
    have hx := (tendsto_xCoord_cofinite E).eventually
      (eventually_pointMap_add_some E G hodd h hQ hQG)
    have ht : Filter.Tendsto (fun P : E.toAffine.Point => P + .some u v hQ)
        Filter.cofinite Filter.cofinite :=
      (show Function.Injective (fun P : E.toAffine.Point => P + .some u v hQ) from
        fun _ _ he => add_right_cancel he).tendsto_cofinite
    filter_upwards [hx, eventually_not_mem_kernel E G,
      ht.eventually (eventually_not_mem_kernel E G)] with P hx hP hS
    cases P with
    | zero => exact (hP G.zero_mem).elim
    | some x y hxy => exact hx y hxy hP hS

/-- The Vélu coordinate map is additive on all ordinary points for a finite odd kernel. -/
theorem pointMap_add (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (h : ∀ P, P ∉ G → (curve E G).toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P Q : E.toAffine.Point) :
    pointMap E G (curve E G) h (P + Q) =
      pointMap E G (curve E G) h P + pointMap E G (curve E G) h Q := by
  let := infinite_points E
  exact Function.map_add_of_cofinite _ (pointMap_add_cofinite E G hodd h) P Q

/-- Additivity is preserved when the Vélu target is presented by an equal equation. -/
theorem pointMap_add_of_curve_eq (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (E' : WeierstrassCurve K) (hcurve : E' = curve E G)
    (h : ∀ P, P ∉ G → E'.toAffine.Nonsingular (xMap E G P) (yMap E G P))
    (P Q : E.toAffine.Point) :
    pointMap E G E' h (P + Q) = pointMap E G E' h P + pointMap E G E' h Q := by
  subst E'
  exact pointMap_add E G hodd h P Q

end WeierstrassCurve.Velu
