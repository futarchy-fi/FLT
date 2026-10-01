/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonDescentUniqueness
public import FLT.Mazur.OneGonGluing
public import FLT.Mazur.OneGonLocalMaps

/-!
# Gluing descended maps on the one-gon

Given a map on the normalization chart factoring through an affine scheme,
with equal endpoint values, and a compatible map on the torus chart, construct
their unique common descent on the actual one-gon scheme. Compatibility is
checked on the normalization, not assumed for the descended maps.

The affine factorization is explicit input. This does not yet prove that
arbitrary normalization maps admit a covering by such factorizations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open FLT.Mazur.PolygonNodePresentation FLT.Mazur.OneGonPinchingAlgebra
open FLT.Mazur.OneGonTransition FLT.Mazur.OneGonGluing

namespace FLT.Mazur.OneGonMapGluing

universe u
variable {K A : Type u} [Field K] [CommRing A]

/-- Descended functions on the unlocalized node chart. -/
def nodeFunctions (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    A →+* B (R := K) :=
  φ.codRestrict (B (R := K)).toSubring fun a ↦
    (mem_B _).mpr (RingHom.congr_fun hφ a)

/-- The morphism on the node chart with the prescribed affine factorization. -/
def nodeMap (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    nodeChart K ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (nodeFunctions φ hφ))

@[reassoc]
theorem normalization_nodeMap (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    toPinching ≫ nodeMap φ hφ = Spec.map (CommRingCat.ofHom φ) := by
  rw [toPinching, nodeMap, ← Spec.map_comp]
  rfl

/-- Inclusion of the overlap into the affine normalization. -/
def punctureToLine : Spec (.of (puncture K)) ⟶ Spec (.of K[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (puncture K)))

@[reassoc]
theorem puncture_toPinching :
    punctureToLine ≫ toPinching = bPuncture K := by
  rw [punctureToLine, toPinching, ← Spec.map_comp]
  rfl

/-- Restrict the prescribed normalization functions to a principal neighborhood. -/
def localizedFunctions (s : B (R := K)) (φ : A →+* K[X]) :
    A →+* OneGonLocalizedPinching.line s :=
  (algebraMap K[X] (OneGonLocalizedPinching.line s)).comp φ

/-- The endpoint agreement persists on every principal neighborhood of the node. -/
theorem localizedFunctions_agree (s : B (R := K)) (hs : bEval s ≠ 0)
    (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    (OneGonLocalizedPinching.atZero s hs).comp (localizedFunctions s φ) =
      (OneGonLocalizedPinching.atOne s hs).comp (localizedFunctions s φ) := by
  apply RingHom.ext
  intro a
  simpa [localizedFunctions, RingHom.comp_apply] using RingHom.congr_fun hφ a

/-- The explicitly constructed local maps are restrictions of the descended node map. -/
theorem nodeMap_on_principal (s : B (R := K)) (hs : bEval s ≠ 0)
    (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart s))) ≫ nodeMap φ hφ =
      OneGonLocalMaps.localMap s hs (localizedFunctions s φ)
        (localizedFunctions_agree s hs φ hφ) := by
  rw [nodeMap, OneGonLocalMaps.localMap, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply OneGonLocalMaps.descend_unique s hs (localizedFunctions s φ)
    (localizedFunctions_agree s hs φ hφ)
  apply RingHom.ext
  intro a
  change OneGonLocalizedPinching.restriction s
    (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart s) (nodeFunctions φ hφ a)) =
      algebraMap K[X] (OneGonLocalizedPinching.line s) (φ a)
  rw [OneGonLocalizedPinching.restriction_algebraMap]
  rfl

/-- The constructed principal-neighborhood maps agree on their actual intersections. -/
theorem principal_maps_compatible (s t : B (R := K))
    (hs : bEval s ≠ 0) (ht : bEval t ≠ 0)
    (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ) :
    pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart s))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart t)))) ≫
      OneGonLocalMaps.localMap s hs (localizedFunctions s φ)
        (localizedFunctions_agree s hs φ hφ) =
    pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart s))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart t)))) ≫
      OneGonLocalMaps.localMap t ht (localizedFunctions t φ)
        (localizedFunctions_agree t ht φ hφ) := by
  rw [← nodeMap_on_principal s hs φ hφ, ← nodeMap_on_principal t ht φ hφ]
  simp only [← Category.assoc, pullback.condition]

variable {X : Scheme.{u}} (φ : A →+* K[X])
    (hφ : (evalRingHom 0).comp φ = (evalRingHom 1).comp φ)
    (j : Spec (.of A) ⟶ X) (g : torusChart K ⟶ X)
    (h : punctureToLine ≫ Spec.map (CommRingCat.ofHom φ) ≫ j = toTorus K ≫ g)

include h in
/-- Agreement of the normalized maps implies agreement of the descended charts. -/
theorem overlap_compatible :
    bPuncture K ≫ nodeMap φ hφ ≫ j = toTorus K ≫ g := by
  rw [← puncture_toPinching, Category.assoc, normalization_nodeMap_assoc]
  exact h

/-- Glue the explicitly descended node map and the original torus map. -/
def gluedMap : scheme K ⟶ X :=
  pushout.desc (nodeMap φ hφ ≫ j) g (overlap_compatible φ hφ j g h)

@[reassoc (attr := simp)]
theorem node_gluedMap :
    node K ≫ gluedMap φ hφ j g h = nodeMap φ hφ ≫ j :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_gluedMap :
    torus K ≫ gluedMap φ hφ j g h = g :=
  pushout.inr_desc _ _ _

/-- The glued morphism recovers the original map on the normalization chart. -/
theorem normalization_gluedMap :
    toPinching ≫ node K ≫ gluedMap φ hφ j g h =
      Spec.map (CommRingCat.ofHom φ) ≫ j := by
  rw [node_gluedMap φ hφ j g h, normalization_nodeMap_assoc φ hφ j]

/-- Restricting the glued morphism recovers the constructed principal local map. -/
theorem principal_gluedMap (s : B (R := K)) (hs : bEval s ≠ 0) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (B (R := K)) (OneGonLocalizedPinching.chart s))) ≫
        node K ≫ gluedMap φ hφ j g h =
      OneGonLocalMaps.localMap s hs (localizedFunctions s φ)
        (localizedFunctions_agree s hs φ hφ) ≫ j := by
  rw [node_gluedMap, ← Category.assoc, nodeMap_on_principal]

/-- The normalization and torus equations uniquely determine the global morphism. -/
theorem gluedMap_unique (d : scheme K ⟶ X)
    (hd : toPinching ≫ node K ≫ d = Spec.map (CommRingCat.ofHom φ) ≫ j)
    (hg : torus K ≫ d = g) : d = gluedMap φ hφ j g h := by
  apply pushout.hom_ext
  · change node K ≫ d = node K ≫ gluedMap φ hφ j g h
    rw [node_gluedMap]
    apply (cancel_epi (toPinching (R := K))).mp
    simpa only [Category.assoc, normalization_nodeMap_assoc] using hd
  · exact hg.trans (torus_gluedMap φ hφ j g h).symm

end FLT.Mazur.OneGonMapGluing
