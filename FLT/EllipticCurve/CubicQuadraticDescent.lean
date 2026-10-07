/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicQuadraticOverlap
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Effective descent through a quadratic covering

The sign charts of the actual kernel pair show that a sign-invariant
morphism coequalizes its projections. The finite étale covering is an
effective epimorphism, so this produces a unique descended morphism
to any scheme. This is a categorical quotient property, with no
affineness restriction on the target and no domain assumption on the base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (d : Rˣ)

/-- The actual sign involution on the quadratic covering scheme. -/
def quadraticEtaleSignMorphism :
    Spec (.of (QuadraticEtaleRing d)) ⟶ Spec (.of (QuadraticEtaleRing d)) :=
  Spec.map (CommRingCat.ofHom (quadraticEtaleNeg d).toRingHom)

/-- The sign involution preserves the coefficient base. -/
theorem quadraticEtaleSignMorphism_over :
    quadraticEtaleSignMorphism d ≫ quadraticEtaleCover d = quadraticEtaleCover d := by
  rw [quadraticEtaleSignMorphism, quadraticEtaleCover, ← Spec.map_comp]
  congr 1
  ext x
  exact (quadraticEtaleNeg d).commutes x

/-- Applying the sign involution twice is the identity. -/
theorem quadraticEtaleSignMorphism_involutive :
    quadraticEtaleSignMorphism d ≫ quadraticEtaleSignMorphism d = 𝟙 _ := by
  rw [quadraticEtaleSignMorphism, ← Spec.map_comp]
  have h := congrArg AlgHom.toRingHom (quadraticEtaleNeg_comp_self d)
  change (quadraticEtaleNeg d).toRingHom.comp (quadraticEtaleNeg d).toRingHom =
    RingHom.id _ at h
  change Spec.map (CommRingCat.ofHom
    ((quadraticEtaleNeg d).toRingHom.comp (quadraticEtaleNeg d).toRingHom)) = _
  rw [h]
  exact Spec.map_id _

/-- A sign-invariant map coequalizes the actual kernel-pair projections. -/
theorem quadraticInvariantMap_relation (h2 : IsUnit (2 : R)) {X : Scheme.{u}}
    (f : Spec (.of (QuadraticEtaleRing d)) ⟶ X)
    (hf : quadraticEtaleSignMorphism d ≫ f = f) :
    pullback.fst (quadraticEtaleCover d) (quadraticEtaleCover d) ≫ f =
      pullback.snd (quadraticEtaleCover d) (quadraticEtaleCover d) ≫ f := by
  apply (quadraticOverlapCover d h2).hom_ext
  intro i
  rw [quadraticOverlapCover_f]
  cases i
  · rw [← Category.assoc, quadraticOverlapChartMap_opposite]
    simpa only [Category.assoc, quadraticEtaleSignMorphism] using
      congrArg (fun k => quadraticOverlapChartMap d false ≫ pullback.snd _ _ ≫ k) hf
  · rw [← Category.assoc, quadraticOverlapChartMap_equal, Category.assoc]

/-- Sign invariance identifies every pair of maps above the same base map. -/
theorem quadraticInvariantMap_relations (h2 : IsUnit (2 : R)) {X Z : Scheme.{u}}
    (f : Spec (.of (QuadraticEtaleRing d)) ⟶ X)
    (hf : quadraticEtaleSignMorphism d ≫ f = f)
    (g₁ g₂ : Z ⟶ Spec (.of (QuadraticEtaleRing d)))
    (h : g₁ ≫ quadraticEtaleCover d = g₂ ≫ quadraticEtaleCover d) :
    g₁ ≫ f = g₂ ≫ f := by
  have ht := congrArg (fun k => pullback.lift g₁ g₂ h ≫ k)
    (quadraticInvariantMap_relation d h2 f hf)
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using ht

variable [Nontrivial R] [Fact (IsUnit (2 : R))]

instance quadraticEtaleCoverEffectiveEpi : EffectiveEpi (quadraticEtaleCover d) := by
  infer_instance

/-- The descended morphism associated to a sign-invariant map. -/
def quadraticEtaleDesc {X : Scheme.{u}}
    (f : Spec (.of (QuadraticEtaleRing d)) ⟶ X)
    (hf : quadraticEtaleSignMorphism d ≫ f = f) : Spec (.of R) ⟶ X :=
  EffectiveEpi.desc (quadraticEtaleCover d) f
    (fun g₁ g₂ h => quadraticInvariantMap_relations d Fact.out f hf g₁ g₂ h)

/-- The descended morphism recovers the original map on the covering. -/
@[reassoc (attr := simp)]
theorem quadraticEtaleDesc_fac {X : Scheme.{u}}
    (f : Spec (.of (QuadraticEtaleRing d)) ⟶ X)
    (hf : quadraticEtaleSignMorphism d ≫ f = f) :
    quadraticEtaleCover d ≫ quadraticEtaleDesc d f hf = f :=
  EffectiveEpi.fac (quadraticEtaleCover d) f
    (fun g₁ g₂ h => quadraticInvariantMap_relations d Fact.out f hf g₁ g₂ h)

/-- Descent through the quadratic covering is unique. -/
theorem quadraticEtaleDesc_unique {X : Scheme.{u}}
    (f : Spec (.of (QuadraticEtaleRing d)) ⟶ X)
    (hf : quadraticEtaleSignMorphism d ≫ f = f)
    (g : Spec (.of R) ⟶ X) (hg : quadraticEtaleCover d ≫ g = f) :
    g = quadraticEtaleDesc d f hf := by
  apply (cancel_epi (quadraticEtaleCover d)).mp
  rw [quadraticEtaleDesc_fac, hg]

omit [Nontrivial R] [Fact (IsUnit (2 : R))] in
/-- Every map from the base pulls back to a sign-invariant map. -/
theorem quadraticEtaleComposite_invariant {X : Scheme.{u}}
    (g : Spec (.of R) ⟶ X) :
    quadraticEtaleSignMorphism d ≫ quadraticEtaleCover d ≫ g =
      quadraticEtaleCover d ≫ g := by
  rw [← Category.assoc, quadraticEtaleSignMorphism_over]

/-- Maps from the base are exactly sign-invariant maps from its quadratic covering. -/
def quadraticEtaleHomEquiv (X : Scheme.{u}) :
    (Spec (.of R) ⟶ X) ≃
      {f : Spec (.of (QuadraticEtaleRing d)) ⟶ X //
        quadraticEtaleSignMorphism d ≫ f = f} where
  toFun g := ⟨quadraticEtaleCover d ≫ g, quadraticEtaleComposite_invariant d g⟩
  invFun f := quadraticEtaleDesc d f.val f.property
  left_inv g := (quadraticEtaleDesc_unique d _ _ g rfl).symm
  right_inv f := Subtype.ext (quadraticEtaleDesc_fac d f.val f.property)

end WeierstrassCurve.CubicCharts
