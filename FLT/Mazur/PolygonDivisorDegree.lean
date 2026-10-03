/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantDegree
public import FLT.Mazur.PolygonDivisorCoproduct
/-!
# Constant degree of the polygon divisor and its base changes

The affine coordinate comparison proves the existing finite locally free
degree contract, including the scheme-theoretic rank at each base point.
The actual pulled-back divisor retains that degree over an arbitrary scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.PolygonDivisorDegree
open PolygonPinching PolygonBoundaryDivisor FCurve
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

omit [NeZero n] in
/-- The product algebra defines a finite locally free morphism of degree n. -/
theorem coordinate_degree :
    FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap K (Fin n → K)))) n := by
  refine ⟨?_, ?_, ?_, fun x ↦ ?_⟩
  · rw [IsFinite.SpecMap_iff]
    change (algebraMap K (Fin n → K)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap K (Fin n → K)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap K (Fin n → K)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  · rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    simp

include h in
/-- Every marked polygon divisor has finite locally free degree n. -/
theorem degree (a : Fin n → Kˣ) :
    FiniteLocallyFreeDegree ((ideal K n p a).subschemeι ≫ C.hom) n :=
  (finiteLocallyFreeDegree_iff_of_overIso
    (PolygonDivisorCoproduct.coordinateOverIso K n p hn q h a)).mpr (coordinate_degree K n)

include h in
/-- The actual divisor comap retains degree n under arbitrary base change. -/
theorem pullback_degree (a : Fin n → Kˣ) {T : Scheme} (g : T ⟶ Spec (.of K)) :
    FiniteLocallyFreeDegree
      (((ideal K n p a).comap (pullback.fst C.hom g)).subschemeι ≫ pullback.snd C.hom g) n :=
  ((degree K n p hn q h a).baseChange g).of_overIso
    (divisorBaseChangeOverIso C.hom g (ideal K n p a)).symm
end FLT.Mazur.PolygonDivisorDegree
