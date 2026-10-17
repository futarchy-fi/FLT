/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedLaurentProduct
public import FLT.Mazur.PolygonUniversalEdgeGroupLaw
public import FLT.Mazur.PolygonUniversalActionTorus

/-!
# The original double Laurent charts of the closed action product

The full edge of the unchanged Laurent family factors through the actual
torus product, preserving its independent parameter and polygon coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "U" => MultiplicativeGroupScheme.gm K
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "G" => PolygonSplitGroup.model K n
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "A" => K[T;T⁻¹][T;T⁻¹]
local notation "e" => completeClosedLaurentProductIso K n h
local notation "z" => zeroFiberIso K n h
local notation "r" => scalingParameterProjection K 0 n h
local notation "E" => edge K[T;T⁻¹] (LaurentPolynomial.C (0 : K)) n h

/-- The unchanged double Laurent coordinates give a point of the actual torus product. -/
def completeClosedLaurentEdgePair : Spec (.of (A)) ⟶ ((U) ⊗ (U)).left :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : K[T;T⁻¹] →+* A)))
    (Spec.map (CommRingCat.ofHom
      (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : K →+* K[T;T⁻¹])))) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext x : 1
      exact (PolygonScalingNaturality.coeffMap_C
        (LaurentPolynomial.C : K →+* K[T;T⁻¹]) x).symm)

/-- The first projection retains the full independent parameter. -/
@[reassoc] theorem completeClosedLaurentEdgePair_fst :
    completeClosedLaurentEdgePair K ≫ (fst (U) (U)).left =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : K[T;T⁻¹] →+* A)) :=
  pullback.lift_fst _ _ _

/-- The second projection retains the full original polygon coordinate. -/
@[reassoc] theorem completeClosedLaurentEdgePair_snd :
    completeClosedLaurentEdgePair K ≫ (snd (U) (U)).left = Spec.map (CommRingCat.ofHom
      (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : K →+* K[T;T⁻¹]))) :=
  pullback.lift_snd _ _ _

omit [NeZero n] in
/-- Each original closed edge is the literal torus inside its normalization component. -/
@[reassoc] theorem completeClosedEdge_original (i : Fin n) :
    edge K 0 n h i ≫ (z).inv = (torusToComponent K ≫ componentι K n i ≫ P).left := by
  rw [← originalTorus_zeroFiberIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [NeZero n] in
/-- The whole Laurent product comparison preserves each full double Laurent chart. -/
@[reassoc] theorem completeClosedLaurentProductIso_edge (i : Fin n) :
    (E) i ≫ (e).hom = completeClosedLaurentEdgePair K ≫
      ((U) ◁ (torusToComponent K ≫ componentι K n i ≫ P)).left := by
  have hf := congrArg Over.Hom.left
    (whiskerLeft_fst (U) (torusToComponent K ≫ componentι K n i ≫ P))
  have hs := congrArg Over.Hom.left
    (whiskerLeft_snd (U) (torusToComponent K ≫ componentι K n i ≫ P))
  simp only [Over.comp_left] at hf hs
  apply pullback.hom_ext
  · change _ ≫ (fst (U) (C)).left = _ ≫ (fst (U) (C)).left
    rw [Category.assoc, completeClosedLaurentProductIso_fst, edge_toBase]
    rw [Category.assoc, hf]
    exact (completeClosedLaurentEdgePair_fst K).symm
  · change _ ≫ (snd (U) (C)).left = _ ≫ (snd (U) (C)).left
    rw [Category.assoc, completeClosedLaurentProductIso_snd]
    have he := (edge_parameter_isPullback (0 : K) n h
      (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (LaurentPolynomial.C 0) rfl i).w
    change _ ≫ edge K 0 n h i = (E) i ≫ (r) at he
    rw [← Category.assoc, ← he, Category.assoc, completeClosedEdge_original]
    rw [Category.assoc, hs, completeClosedLaurentEdgePair_snd_assoc]
    rfl

end FLT.Mazur.PolygonInfinitesimalStages
