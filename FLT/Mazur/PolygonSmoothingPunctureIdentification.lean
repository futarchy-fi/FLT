/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureCalculus
public import FLT.Mazur.LaurentNilpotentReparametrization

/-!
# Full puncture substitutions are determined by normalized node factors

The coordinate on either puncture detects a full Laurent algebra map.
Consequently both source normalization and terminal rebasing identify the
entire substitutions when their whole-node factors have been identified.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]
local notation "L" => R[T;T⁻¹]

/-- Equality after the original puncture detects the full Laurent algebra map. -/
theorem punctureLaurentMap_cancel (t : R) (b : Bool) {f g : L →ₐ[R] L}
    (h : f.comp (punctureLaurentMap t b) = g.comp (punctureLaurentMap t b)) : f = g := by
  apply LaurentNilpotentReparametrization.hom_ext_positive
  cases b
  · have hh := AlgHom.congr_fun h (rightCoordinate t)
    simpa only [punctureLaurentMap, AlgHom.comp_apply, branchSwapMap_right,
      leftLaurentMap_left] using hh
  · have hh := AlgHom.congr_fun h (leftCoordinate t)
    simpa only [punctureLaurentMap, AlgHom.comp_apply, leftLaurentMap_left] using hh

/-- Normalizing the source of a node factor identifies both complete puncture substitutions. -/
theorem punctureFactor_source_identification (s t : R) (h : s = t)
    (F : ChartRing s ≃ₐ[R] ChartRing t) (G : ChartRing t ≃ₐ[R] ChartRing t)
    (a d : L ≃ₐ[R] L) (b : Bool)
    (hF : F.toAlgHom.toRingHom = G.toAlgHom.toRingHom.comp
      (ringMap (RingHom.id R) s t h))
    (ha : (punctureLaurentMap t b).comp F.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap s b))
    (hd : (punctureLaurentMap t b).comp G.toAlgHom =
      d.toAlgHom.comp (punctureLaurentMap t b)) : a = d := by
  subst s
  rw [ringMap_id, RingHom.comp_id] at hF
  have hFG : F = G := AlgEquiv.ext (fun z ↦ DFunLike.congr_fun hF z)
  rw [hFG, hd] at ha
  exact AlgEquiv.coe_toAlgHom_injective (punctureLaurentMap_cancel t b ha.symm)

/-- Normalizing a rebased target identifies its full terminal puncture substitutions. -/
theorem punctureFactor_rebased_identification (s t : R) (h : s = t)
    (F : ChartRing t ≃ₐ[R] ChartRing s) (G : ChartRing t ≃ₐ[R] ChartRing t)
    (a d : L ≃ₐ[R] L) (b : Bool)
    (hF : (ringMap (RingHom.id R) s t h).comp F.toAlgHom.toRingHom =
      G.toAlgHom.toRingHom)
    (ha : (punctureLaurentMap s b).comp F.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap t b))
    (hd : (punctureLaurentMap t b).comp G.toAlgHom =
      d.toAlgHom.comp (punctureLaurentMap t b)) : a = d := by
  subst s
  rw [ringMap_id, RingHom.id_comp] at hF
  have hFG : F = G := AlgEquiv.ext (fun z ↦ DFunLike.congr_fun hF z)
  rw [hFG, hd] at ha
  exact AlgEquiv.coe_toAlgHom_injective (punctureLaurentMap_cancel t b ha.symm)

end FLT.Mazur.PolygonSmoothing
