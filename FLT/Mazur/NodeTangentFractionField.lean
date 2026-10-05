/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentDepth
public import FLT.Mazur.NodeTangentUnramified
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The quadratic fraction field of the tangent DVR

The generic root algebra is a separable quadratic extension of the original
fraction field. The integral tangent algebra is its DVR, is formally
unramified over the original DVR, and retains the original uniformizer.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing Polynomial AdjoinRoot

/-- A nonzero tangent discriminant makes the tangent quadratic separable. -/
theorem nodeTangentPolynomial_separable {F : Type*} [Field F]
    (W : WeierstrassCurve F) (hb : W.b₂ ≠ 0) : (nodeTangentPolynomial W).Separable := by
  have hp : nodeTangentPolynomial W = C 1 * X ^ 2 + C W.a₁ * X + C (-W.a₂) := by
    simp [nodeTangentPolynomial, sub_eq_add_neg]
  rw [hp, separable_quadratic_iff one_ne_zero]
  simpa [discrim, b₂] using hb

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)

/-- The canonical tangent DVR has a separable quadratic fraction field over K, and the
original uniformizer generates its maximal ideal. All structures are constructed. -/
theorem exists_node_tangent_fraction_field
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R)))
    (hb : IsUnit W.b₂) (π : R) (hπ : maximalIdeal R = Ideal.span {π}) :
    let S := AdjoinRoot (nodeTangentPolynomial W)
    ∃ (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : IsLocalHom (algebraMap R S)) (_ : Algebra.FormallyUnramified R S)
      (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (_ : Algebra R L) (_ : IsScalarTower R K L)
      (_ : Algebra S L) (_ : IsScalarTower R S L) (_ : IsFractionRing S L),
      Module.finrank K L = 2 ∧ maximalIdeal S = Ideal.span {algebraMap R S π} := by
  let P := nodeTangentPolynomial W
  have hm : P.Monic := nodeTangentPolynomial_monic W
  have hi : Irreducible P := hm.irreducible_of_irreducible_map (residue R) P hirr
  let : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  have hd : P.degree ≠ 0 := by rw [nodeTangentPolynomial_degree]; norm_num
  obtain ⟨hmax, hDVR, hlocal⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hm hd hirr
  let := hDVR
  have hmax' : maximalIdeal (AdjoinRoot P) =
      (maximalIdeal R).map (algebraMap R (AdjoinRoot P)) := (eq_maximalIdeal hmax).symm
  let pK := P.map (algebraMap R K)
  let : Fact (Irreducible pK) :=
    ⟨(hm.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hi⟩
  let L := AdjoinRoot pK
  let algSL : Algebra (AdjoinRoot P) L :=
    (AdjoinRoot.map (algebraMap R K) P pK (dvd_refl _)).toAlgebra
  have halg : algebraMap (AdjoinRoot P) L =
      AdjoinRoot.map (algebraMap R K) P pK (dvd_refl _) := RingHom.algebraMap_toAlgebra _
  have htower : IsScalarTower R (AdjoinRoot P) L := .of_algebraMap_eq fun r => by
    rw [halg, AdjoinRoot.algebraMap_eq (f := P), map_of, algebraMap_eq']
    rfl
  have hs : pK.Separable := by
    have h := nodeTangentPolynomial_separable (W.map (algebraMap R K))
      (by simpa only [map_b₂] using (hb.map (algebraMap R K)).ne_zero)
    simpa [nodeTangentPolynomial, pK, P] using h
  refine ⟨inferInstance, hDVR, hlocal, nodeTangentAlgebra_formallyUnramified W hb,
    L, inferInstance, inferInstance, (powerBasis (Fact.out (p := Irreducible pK)).ne_zero).finite,
    isSeparable_of_separable hs, inferInstance, inferInstance, algSL, htower,
    isFractionRing_map hd hmax' (by rw [halg]; exact map_comp_mk (algebraMap R K) rfl),
    ?_, ?_⟩
  · rw [AdjoinRoot.finrank_eq_natDegree, hm.natDegree_map]
    exact natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)
  · rw [hmax', hπ, Ideal.map_span, Set.image_singleton]

end FLT.Mazur
