/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticNodeCorrectionLift
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality

/-!
# Simultaneous arithmetic lifts on both branches of one node

Reflect the second whole-node correction, then compose the first correction
on its changed source smoothing. Both branches share a single node at every
order, and the entire composition respects the arithmetic quotient maps.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- Intertwining squares remain compatible after conjugation at source and target. -/
theorem correctionConjugate_square {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (F : A →+* B) (G : C →+* D) (P : A →+* C) (Q : B →+* D)
    (a : A →+* A) (b : B →+* B) (c : C →+* C) (d : D →+* D)
    (hc : G.comp c = d.comp G) (hP : G.comp P = Q.comp F) (ha : F.comp a = b.comp F) :
    G.comp (c.comp (P.comp a)) = (d.comp (Q.comp b)).comp F := by
  rw [← RingHom.comp_assoc, hc, RingHom.comp_assoc, ← RingHom.comp_assoc a P G,
    hP, RingHom.comp_assoc a F Q, ha]
  simp only [RingHom.comp_assoc]

/-- Two successive intertwining squares compose. -/
theorem correctionCompose_square {A B C D E F : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E] [CommRing F]
    (f : A →+* B) (g : C →+* D) (h : E →+* F)
    (p : A →+* C) (q : B →+* D) (r : C →+* E) (s : D →+* F)
    (hr : h.comp r = s.comp g) (hp : g.comp p = q.comp f) :
    h.comp (r.comp p) = (s.comp q).comp f := by
  rw [← RingHom.comp_assoc, hr, RingHom.comp_assoc, hp, ← RingHom.comp_assoc]

/-- Reflect a full arithmetic correction across the original interchange of node coordinates. -/
irreducible_def reflectedCorrectionNodeFactor (m : ℕ) (t : Quotient R π m) (q : R[T;T⁻¹]) :
    ChartRing (correctionSmoothing R π m t q) ≃ₐ[Quotient R π m] ChartRing t :=
  (branchSwap (correctionSmoothing R π m t q)).trans
    ((correctionNodeFactor R π m t q).trans (branchSwap t))

/-- The reflected whole-node lift commutes with each actual arithmetic quotient. -/
theorem reflectedCorrectionNodeFactor_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : R[T;T⁻¹]) :
    (ringMap (restriction R π m).toRingHom t s hs).comp
        (reflectedCorrectionNodeFactor R π (m + 1) t q).toAlgHom.toRingHom =
      (reflectedCorrectionNodeFactor R π m s q).toAlgHom.toRingHom.comp
        (ringMap (restriction R π m).toRingHom
          (correctionSmoothing R π (m + 1) t q) (correctionSmoothing R π m s q)
          (correctionSmoothing_restriction R π m t s hs q)) := by
  rw [reflectedCorrectionNodeFactor_def, reflectedCorrectionNodeFactor_def]
  exact correctionConjugate_square
    (ringMap (restriction R π m).toRingHom
      (correctionSmoothing R π (m + 1) t q) (correctionSmoothing R π m s q)
      (correctionSmoothing_restriction R π m t s hs q))
    (ringMap (restriction R π m).toRingHom t s hs)
    (correctionNodeFactor R π (m + 1) t q).toAlgHom.toRingHom
    (correctionNodeFactor R π m s q).toAlgHom.toRingHom
    (branchSwapMap _).toRingHom (branchSwapMap _).toRingHom
    (branchSwapMap t).toRingHom (branchSwapMap s).toRingHom
    (ringMap_branchSwap _ _ _ _).symm
    (correctionNodeFactor_restriction R π m t s hs q)
    (ringMap_branchSwap _ _ _ _).symm


/-- The common source smoothing after correcting both branches in their specified order. -/
def twoBranchCorrectionSmoothing (m : ℕ) (t : Quotient R π m) (q : Bool → R[T;T⁻¹]) :
    Quotient R π m :=
  correctionSmoothing R π m (correctionSmoothing R π m t (q false)) (q true)

/-- Both full boundary corrections live on one whole node, with a single common smoothing. -/
irreducible_def twoBranchCorrectionNodeFactor (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) :
    ChartRing (twoBranchCorrectionSmoothing R π m t q) ≃ₐ[Quotient R π m] ChartRing t :=
  (correctionNodeFactor R π m (correctionSmoothing R π m t (q false)) (q true)).trans
    (reflectedCorrectionNodeFactor R π m t (q false))

/-- The common changed smoothing is compatible with the original arithmetic restrictions. -/
theorem twoBranchCorrectionSmoothing_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : Bool → R[T;T⁻¹]) :
    restriction R π m (twoBranchCorrectionSmoothing R π (m + 1) t q) =
      twoBranchCorrectionSmoothing R π m s q :=
  correctionSmoothing_restriction R π m _ _
    (correctionSmoothing_restriction R π m t s hs (q false)) (q true)

/-- The complete two-branch lift, rather than just its boundary values, descends at every order. -/
theorem twoBranchCorrectionNodeFactor_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : Bool → R[T;T⁻¹]) :
    (ringMap (restriction R π m).toRingHom t s hs).comp
        (twoBranchCorrectionNodeFactor R π (m + 1) t q).toAlgHom.toRingHom =
      (twoBranchCorrectionNodeFactor R π m s q).toAlgHom.toRingHom.comp
        (ringMap (restriction R π m).toRingHom
          (twoBranchCorrectionSmoothing R π (m + 1) t q) (twoBranchCorrectionSmoothing R π m s q)
          (twoBranchCorrectionSmoothing_restriction R π m t s hs q)) := by
  rw [twoBranchCorrectionNodeFactor_def, twoBranchCorrectionNodeFactor_def]
  exact correctionCompose_square
    (ringMap (restriction R π m).toRingHom
      (twoBranchCorrectionSmoothing R π (m + 1) t q) (twoBranchCorrectionSmoothing R π m s q)
      (twoBranchCorrectionSmoothing_restriction R π m t s hs q))
    (ringMap (restriction R π m).toRingHom
      (correctionSmoothing R π (m + 1) t (q false)) (correctionSmoothing R π m s (q false))
      (correctionSmoothing_restriction R π m t s hs (q false)))
    (ringMap (restriction R π m).toRingHom t s hs) _ _ _ _
    (reflectedCorrectionNodeFactor_restriction R π m t s hs (q false))
    (correctionNodeFactor_restriction R π m _ _
      (correctionSmoothing_restriction R π m t s hs (q false)) (q true))


/-- At first order both smoothing drifts vanish when the original smoothing is annihilated. -/
theorem twoBranchCorrectionSmoothing_first (t : Quotient R π 1)
    (ht : parameter R π 1 * t = 0) (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionSmoothing R π 1 t q = t := by
  unfold twoBranchCorrectionSmoothing
  rw [correctionSmoothing_first R π t ht, correctionSmoothing_first R π t ht]

end FLT.Mazur.PolygonArithmeticStages
