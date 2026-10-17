/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureCalculus
public import FLT.Mazur.PolygonSmoothingNilpotentPunctureNaturality

/-!
# Full puncture naturality follows from the whole-node square

The selected node coordinate maps to T on its puncture. Therefore a
coefficient-compatible whole-node map determines the coefficient square of
its complete Laurent substitution, with no finite-support truncation.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original coordinate used on each puncture. -/
def punctureCoordinate (t : R) : Bool → ChartRing t
  | true => leftCoordinate t
  | false => rightCoordinate t

/-- The selected coordinate is the full positive Laurent generator. -/
theorem punctureLaurentMap_coordinate (t : R) (b : Bool) :
    punctureLaurentMap t b (punctureCoordinate t b) = T 1 := by
  cases b
  · exact (congrArg (leftLaurentMap t) (branchSwapMap_right t)).trans (leftLaurentMap_left t)
  · exact leftLaurentMap_left t

/-- Coefficient restriction preserves the selected node coordinate. -/
theorem ringMap_punctureCoordinate (f : R →+* S) (t : R) (s : S) (hs : f t = s)
    (b : Bool) : ringMap f t s hs (punctureCoordinate t b) = punctureCoordinate s b := by
  cases b
  · exact ringMap_right f t s hs
  · exact ringMap_left f t s hs

/-- Both original full punctures commute with arbitrary coefficient change. -/
theorem ringMap_punctureLaurent (f : R →+* S) (t : R) (s : S) (hs : f t = s)
    (b : Bool) :
    (punctureLaurentMap s b).toRingHom.comp (ringMap f t s hs) =
      (coeffMap f).comp (punctureLaurentMap t b).toRingHom := by
  cases b
  · exact ringMap_rightLaurent f t s hs
  · exact ringMap_leftLaurent f t s hs

/-- A full puncture factorization evaluates the chosen node coordinate at the actual unit. -/
theorem punctureFactor_coordinate (s t : R) (f : ChartRing s →ₐ[R] ChartRing t)
    (a : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f = a.comp (punctureLaurentMap s b)) :
    punctureLaurentMap t b (f (punctureCoordinate s b)) = a (T 1) := by
  have h := AlgHom.congr_fun hf (punctureCoordinate s b)
  simpa only [AlgHom.comp_apply, punctureLaurentMap_coordinate] using h

/-- The full Laurent coefficient square is forced by the original whole-node square. -/
theorem punctureFactor_naturality (F : R →+* S) (r t : R) (s v : S)
    (hr : F r = s) (ht : F t = v)
    (f : ChartRing r ≃ₐ[R] ChartRing t) (g : ChartRing s ≃ₐ[S] ChartRing v)
    (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (d : S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap r b))
    (hg : (punctureLaurentMap v b).comp g.toAlgHom =
      d.toAlgHom.comp (punctureLaurentMap s b))
    (hnode : (ringMap F t v ht).comp f.toAlgHom.toRingHom =
      g.toAlgHom.toRingHom.comp (ringMap F r s hr)) :
    (coeffMap F).comp a.toAlgHom.toRingHom = d.toAlgHom.toRingHom.comp (coeffMap F) := by
  apply LaurentUnitSubstitutionNaturality.equiv_naturality
  apply Units.ext
  change coeffMap F (a (T 1)) = d (T 1)
  have hp := DFunLike.congr_fun (ringMap_punctureLaurent F t v ht b)
    (f (punctureCoordinate r b))
  change punctureLaurentMap v b (ringMap F t v ht (f (punctureCoordinate r b))) =
    coeffMap F (punctureLaurentMap t b (f (punctureCoordinate r b))) at hp
  have hn := DFunLike.congr_fun hnode (punctureCoordinate r b)
  change ringMap F t v ht (f (punctureCoordinate r b)) =
    g (ringMap F r s hr (punctureCoordinate r b)) at hn
  have hc := punctureFactor_coordinate r t f.toAlgHom a.toAlgHom b hf
  change punctureLaurentMap t b (f (punctureCoordinate r b)) = a (T 1) at hc
  rw [hc] at hp
  rw [← hp, hn, ringMap_punctureCoordinate]
  exact punctureFactor_coordinate s v g.toAlgHom d.toAlgHom b hg

end FLT.Mazur.PolygonSmoothing
