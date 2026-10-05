/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentValuationModel

/-!
# Integral and generic conjugation of the tangent extension

The root involution extends to an automorphism of the quadratic fraction field
fixing the original field. Its restriction to the actual valuation subring is
the transported integral involution, and it conjugates the sheared equation to
the tangent-swap equation.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (L : Type*) [Field L]
  [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))]
  [Algebra (AdjoinRoot (nodeTangentPolynomial W)) L]
  [IsFractionRing (AdjoinRoot (nodeTangentPolynomial W)) L]

/-- Integral conjugation on the actual tangent valuation subring. -/
noncomputable def nodeTangentValuationConjugation :
    nodeTangentValuationSubring A W L ≃+* nodeTangentValuationSubring A W L :=
  (nodeTangentValuationEquiv A W L).symm.trans
    ((nodeTangentConjugation W).toRingEquiv.trans (nodeTangentValuationEquiv A W L))

/-- The realized integral conjugation agrees with the root involution. -/
theorem nodeTangentValuationConjugation_equiv (s : AdjoinRoot (nodeTangentPolynomial W)) :
    nodeTangentValuationConjugation A W L (nodeTangentValuationEquiv A W L s) =
      nodeTangentValuationEquiv A W L (nodeTangentConjugation W s) := by
  simp [nodeTangentValuationConjugation]

/-- Integral conjugation fixes the image of every original coefficient. -/
theorem nodeTangentValuationConjugation_base (a : A) :
    nodeTangentValuationConjugation A W L
        (nodeTangentValuationEquiv A W L (algebraMap A _ a)) =
      nodeTangentValuationEquiv A W L (algebraMap A _ a) := by
  rw [nodeTangentValuationConjugation_equiv, AlgEquiv.commutes]

/-- The transported integral conjugation is still an involution. -/
theorem nodeTangentValuationConjugation_involutive :
    Function.Involutive (nodeTangentValuationConjugation A W L) := by
  intro x
  obtain ⟨s, rfl⟩ := (nodeTangentValuationEquiv A W L).surjective x
  rw [nodeTangentValuationConjugation_equiv, nodeTangentValuationConjugation_equiv]
  exact congrArg (nodeTangentValuationEquiv A W L) (nodeTangentConjugationHom_involutive W s)

/-- Tangent-swap equations commute with arbitrary coefficient maps. -/
theorem nodeTangentSwap_map {R S : Type*} [CommRing R] [CommRing S]
    (V : WeierstrassCurve R) (f : R →+* S) :
    (nodeTangentSwap V • V).map f = nodeTangentSwap (V.map f) • V.map f := by
  rw [← map_variableChange]
  congr 1
  ext <;> simp [nodeTangentSwap, VariableChange.map]

/-- Conjugation of the realized sheared model is exactly tangent exchange. -/
theorem nodeTangentValuationShear_conjugate :
    (nodeTangentValuationShear A W L).map
        (nodeTangentValuationConjugation A W L).toRingHom =
      nodeTangentSwap (nodeTangentValuationShear A W L) •
        nodeTangentValuationShear A W L := by
  have hc : (nodeTangentValuationConjugation A W L).toRingHom.comp
        (nodeTangentValuationEquiv A W L).toRingHom =
      (nodeTangentValuationEquiv A W L).toRingHom.comp
        (nodeTangentConjugation W).toRingHom := by
    apply RingHom.ext
    intro s
    exact nodeTangentValuationConjugation_equiv A W L s
  rw [nodeTangentValuationShear, map_map, hc, ← map_map,
    nodeTangentShear_conjugate, nodeTangentSwap_map]

variable [Algebra A L] [IsScalarTower A (AdjoinRoot (nodeTangentPolynomial W)) L]
  [Algebra K L] [IsScalarTower A K L]

/-- The integral tangent involution extends to an automorphism fixing K. -/
noncomputable def nodeTangentFieldConjugation : L ≃ₐ[K] L :=
  IsFractionRing.fieldEquivOfAlgEquiv K L L (nodeTangentConjugation W)

omit [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))] in
/-- The generic conjugation restricts to the integral root involution. -/
theorem nodeTangentFieldConjugation_algebraMap (s : AdjoinRoot (nodeTangentPolynomial W)) :
    nodeTangentFieldConjugation A W L (algebraMap _ L s) =
      algebraMap _ L (nodeTangentConjugation W s) :=
  IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L _ s

/-- Generic and realized integral conjugation are compatible. -/
theorem nodeTangentFieldConjugation_coe (s : nodeTangentValuationSubring A W L) :
    nodeTangentFieldConjugation A W L (s : L) =
      (nodeTangentValuationConjugation A W L s : L) := by
  obtain ⟨s, rfl⟩ := (nodeTangentValuationEquiv A W L).surjective s
  rw [nodeTangentValuationConjugation_equiv]
  exact nodeTangentFieldConjugation_algebraMap A W L s

omit [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))] in
/-- The generic tangent conjugation has order dividing two. -/
theorem nodeTangentFieldConjugation_involutive :
    Function.Involutive (nodeTangentFieldConjugation A W L) := by
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective
    (AdjoinRoot (nodeTangentPolynomial W)) x
  simp only [map_div₀, nodeTangentFieldConjugation_algebraMap]
  congr 1 <;> exact congrArg (algebraMap _ L) (nodeTangentConjugationHom_involutive W _)

omit [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))] in
/-- The field involution is nontrivial when the tangent discriminant is a unit. -/
theorem nodeTangentFieldConjugation_ne_refl (hb : IsUnit W.b₂) :
    nodeTangentFieldConjugation A W L ≠ AlgEquiv.refl := by
  intro h
  apply nodeTangentConjugation_ne_refl W hb
  ext s
  apply IsFractionRing.injective (AdjoinRoot (nodeTangentPolynomial W)) L
  rw [← nodeTangentFieldConjugation_algebraMap, h]
  rfl

/-- The generic involution preserves and reflects the actual valuation subring. -/
theorem nodeTangentFieldConjugation_mem_iff (x : L) :
    nodeTangentFieldConjugation A W L x ∈ nodeTangentValuationSubring A W L ↔
      x ∈ nodeTangentValuationSubring A W L := by
  have hp (y : L) (hy : y ∈ nodeTangentValuationSubring A W L) :
      nodeTangentFieldConjugation A W L y ∈ nodeTangentValuationSubring A W L := by
    rw [nodeTangentFieldConjugation_coe A W L ⟨y, hy⟩]
    exact (nodeTangentValuationConjugation A W L ⟨y, hy⟩).property
  refine ⟨fun h => ?_, hp x⟩
  simpa only [nodeTangentFieldConjugation_involutive A W L x] using hp _ h

end FLT.Mazur
