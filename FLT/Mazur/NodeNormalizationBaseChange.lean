/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PinchingChartBaseChange
public import FLT.Mazur.ProjectiveLineProductCharts
public import Mathlib.RingTheory.TensorProduct.Pi
/-!
# Base change for the two-branch normalization

Tensor-product coordinates identify the product of polynomial branches after
coefficient extension and give a cartesian square over the relative node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Polynomial
universe u
namespace FLT.Mazur.NodeNormalizationBaseChange
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
open PinchingChartBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Scalar extension of the two polynomial branches. -/
def tensorIso : S ⊗[K] (K[X] × K[X]) ≃ₐ[S] S[X] × S[X] :=
  (Algebra.TensorProduct.prodRight K S S K[X] K[X]).trans
    (AlgEquiv.prodCongr (polyEquivTensor' K S).symm (polyEquivTensor' K S).symm)

/-- The actual scheme pullback in product-polynomial coordinates. -/
def productIso :
    pullback (parameter K S) (Spec.map (CommRingCat.ofHom (algebraMap K (K[X] × K[X])))) ≅
      Spec (.of (S[X] × S[X])) :=
  pullbackSpecIso K S (K[X] × K[X]) ≪≫
    Scheme.Spec.mapIso (tensorIso K S).symm.toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)] theorem productIso_inv_fst :
    (productIso K S).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S[X] × S[X]))) := by
  change Spec.map (CommRingCat.ofHom (tensorIso K S).toAlgHom.toRingHom) ≫
    (pullbackSpecIso K S (K[X] × K[X])).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact AlgHom.comp_algebraMap (tensorIso K S).toAlgHom

/-- Coefficient extension on the pair of polynomial branches. -/
def coeff : K[X] × K[X] →+* S[X] × S[X] :=
  RingHom.prodMap (Polynomial.mapRingHom (algebraMap K S))
    (Polynomial.mapRingHom (algebraMap K S))

@[reassoc (attr := simp)] theorem productIso_inv_snd :
    (productIso K S).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (coeff K S)) := by
  change Spec.map (CommRingCat.ofHom (tensorIso K S).toAlgHom.toRingHom) ≫
    (pullbackSpecIso K S (K[X] × K[X])).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change tensorIso K S (1 ⊗ₜ[K] p) = _
  change ((polyEquivTensor' K S).symm
    ((Algebra.TensorProduct.prodRight K S S K[X] K[X]) (1 ⊗ₜ[K] p)).1,
    (polyEquivTensor' K S).symm
    ((Algebra.TensorProduct.prodRight K S S K[X] K[X]) (1 ⊗ₜ[K] p)).2) = _
  rw [Algebra.TensorProduct.prodRight_tmul]
  change ((1 : S) • p.1.map (algebraMap K S), (1 : S) • p.2.map (algebraMap K S)) = _
  simp only [one_smul]
  rfl

/-- The normalization inclusion of the affine node. -/
def normalization (R : Type u) [CommRing R] :
    Spec (.of (R[X] × R[X])) ⟶ PolygonNodeBranches.node R :=
  Spec.map (CommRingCat.ofHom (PolygonNodeEqualizer.A (R := R)).val.toRingHom)

@[reassoc] theorem normalization_coeff :
    normalization S ≫ Spec.map (CommRingCat.ofHom
      (PolygonNodeScalarExtension.coeffMap (R := K) (S := S)).toRingHom) =
      Spec.map (CommRingCat.ofHom (coeff K S)) ≫ normalization K := by
  rw [normalization, normalization, ← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc] theorem normalization_base (R : Type u) [CommRing R] :
    normalization R ≫ nodeBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (R[X] × R[X]))) := by
  rw [normalization, nodeBase, ← Spec.map_comp]
  rfl

theorem coefficient_isPullback : IsPullback (normalization S)
    (Spec.map (CommRingCat.ofHom (coeff K S)))
    (Spec.map (CommRingCat.ofHom
      (PolygonNodeScalarExtension.coeffMap (R := K) (S := S)).toRingHom))
    (normalization K) := by
  have hA : IsPullback (nodeBase S)
      (Spec.map (CommRingCat.ofHom
        (PolygonNodeScalarExtension.coeffMap (R := K) (S := S)).toRingHom))
      (parameter K S) (nodeBase K) := by
    exact IsPullback.of_iso_pullback ⟨by
      rw [← nodeProductIso_inv_fst K S, ← nodeProductIso_inv_snd K S]
      simp only [Category.assoc, pullback.condition]⟩ (nodeProductIso K S).symm
        (nodeProductIso_inv_fst K S) (nodeProductIso_inv_snd K S)
  apply IsPullback.of_right (h₁₂ := nodeBase S) (h₂₂ := nodeBase K) _
    (normalization_coeff K S) hA
  rw [normalization_base, normalization_base]
  exact IsPullback.of_iso_pullback ⟨by
    rw [← productIso_inv_fst K S, ← productIso_inv_snd K S]
    simp only [Category.assoc, pullback.condition]⟩ (productIso K S).symm
      (productIso_inv_fst K S) (productIso_inv_snd K S)
end FLT.Mazur.NodeNormalizationBaseChange
