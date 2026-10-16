/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonLabels
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialPolygon
public import FLT.Mazur.WeierstrassDividedRetainedPolygonNaturality

/-!
# Both full initial neighborhoods map to their intended polygon labels

The source remains the actual open D(q+a₁). Each map preserves the smoothing
and coefficient ring, reversing the opposite branch's coordinates as on its arm.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)
  [Fact (IsNilpotent s)] (k : ℕ)

/-- The complete initial node neighborhood maps to its original branch's cyclic label. -/
def initialPolygonMap (b : Bool) : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonInfinitesimal.scheme R s (2 * k + 3) (by omega) :=
  initialPolygonChart W s ≫ (if b then (branchSwapIso R s).hom else 𝟙 _) ≫
    PolygonInfinitesimal.chart R s (2 * k + 3) (by omega) (initialPolygonIndex k b)

instance initialPolygonMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (initialPolygonMap W s k b) := by
  unfold initialPolygonMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Both complete initial comparisons preserve the original base. -/
@[reassoc] theorem initialPolygonMap_base (b : Bool) :
    initialPolygonMap W s k b ≫ PolygonInfinitesimal.toBase R s (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W s))) := by
  cases b <;> simp only [initialPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.assoc,
    PolygonInfinitesimal.chart_toBase, retainedPolygonSwap_base, Category.id_comp]
  all_goals exact initialPolygonChart_structure W s

variable {S : Type u} [CommRing S] (f : R →+* S) [Fact (IsNilpotent (f s))]

/-- Both entire oriented initial neighborhoods retain every coefficient under base change. -/
@[reassoc] theorem initialPolygonMap_parameterProjection (b : Bool) :
    initialPolygonMap (W.map f) (f s) k b ≫
      PolygonInfinitesimal.parameterProjection f s (f s) rfl (2 * k + 3) (by omega) =
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫
      initialPolygonMap W s k b := by
  cases b <;> simp only [initialPolygonMap, Bool.false_eq_true, ↓reduceIte,
    Category.assoc, Category.id_comp]
  · rw [PolygonInfinitesimal.chart_parameterProjection,
      ← initialPolygonChart_coefficients_assoc]
  · rw [PolygonInfinitesimal.chart_parameterProjection, branchSwapIso_ringMap_assoc,
      ← initialPolygonChart_coefficients_assoc]

omit [Fact (IsNilpotent (f s))] in
/-- Explicit target transport keeps both original initial labels and the full base map. -/
@[reassoc] theorem initialPolygonMap_parameterProjectionTo
    (U : WeierstrassCurve S) (s' : S) [Fact (IsNilpotent s')]
    (hW : W.map f = U) (hs : f s = s') (b : Bool) :
    initialPolygonMap U s' k b ≫
      PolygonInfinitesimal.parameterProjection f s s' hs (2 * k + 3) (by omega) =
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMapTo f W s U s' hW hs)) ≫
      initialPolygonMap W s k b := by
  subst U s'
  exact initialPolygonMap_parameterProjection W s k f b

end FLT.Mazur.WeierstrassDividedDepth
