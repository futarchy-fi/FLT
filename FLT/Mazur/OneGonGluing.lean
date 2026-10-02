/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonOverlap
public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Gluing the two charts of the one-gon

Glue the actual equalizer chart for pinching zero and one to the multiplicative
chart using the coordinate t/(t-1). Both inclusions are open and jointly cover
the constructed scheme. Identifying this scheme with the cyclic pinching
of the projective line, and proving its genus and group action, remain separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial

namespace FLT.Mazur.OneGonTransition

variable (R : Type*) [CommRing R]

@[simp]
theorem torusRestriction_C (r : R) :
    torusRestriction R (LaurentPolynomial.C r) = algebraMap R (puncture R) r := by
  have h := (localizationEquiv R).symm.commutes (Polynomial.C r)
  rw [IsScalarTower.algebraMap_apply R[X] R[T;T⁻¹] (torusPuncture R)] at h
  have hc : algebraMap R[X] R[T;T⁻¹] (Polynomial.C r) = LaurentPolynomial.C r := by
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
  rw [hc] at h
  exact h

@[simp]
theorem overlapMap_C (r : R) :
    overlapMap R (LaurentPolynomial.C r) = algebraMap R (puncture R) r := by
  simp [overlapMap]

end OneGonTransition

namespace OneGonGluing

open PolygonNodePresentation OneGonTransition

variable (K : Type*) [Field K]

/-- The actual affine chart pinching zero and one on the normalization. -/
abbrev nodeChart := Spec (.of (B (R := K)))

/-- The complementary multiplicative chart. -/
abbrev torusChart := Spec (.of K[T;T⁻¹])

/-- The scheme obtained from the specified one-gon overlap. -/
def scheme : Scheme := pushout (bPuncture K) (toTorus K)

/-- Inclusion of the pinched affine chart. -/
def node : nodeChart K ⟶ scheme K := pushout.inl _ _

/-- Inclusion of the multiplicative chart. -/
def torus : torusChart K ⟶ scheme K := pushout.inr _ _

instance node_isOpenImmersion : IsOpenImmersion (node K) := by
  change IsOpenImmersion (colimit.ι (span (bPuncture K) (toTorus K)) WalkingSpan.left)
  infer_instance

instance torus_isOpenImmersion : IsOpenImmersion (torus K) := by
  change IsOpenImmersion (colimit.ι (span (bPuncture K) (toTorus K)) WalkingSpan.right)
  infer_instance

/-- The two chart inclusions agree on the prescribed puncture. -/
theorem overlap_condition : bPuncture K ≫ node K = toTorus K ≫ torus K :=
  pushout.condition

/-- Every point of the constructed scheme lies in one of its two charts. -/
theorem charts_cover (x : scheme K) :
    (∃ y : nodeChart K, node K y = x) ∨ ∃ y : torusChart K, torus K y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (bPuncture K) (toTorus K)) x
  cases i with
  | none =>
    left
    refine ⟨bPuncture K y, ?_⟩
    change (bPuncture K ≫ node K) y = x
    rw [show bPuncture K ≫ node K =
      colimit.ι (span (bPuncture K) (toTorus K)) WalkingSpan.zero from
        colimit.w (span (bPuncture K) (toTorus K)) WalkingSpan.Hom.fst]
    exact hy
  | some i =>
    cases i with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

/-- Structure morphism of the multiplicative chart. -/
def torusToBase : torusChart K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- Both overlap morphisms preserve the coefficient field. -/
theorem overlap_toBase : bPuncture K ≫ bToBase K = toTorus K ≫ torusToBase K := by
  have h : (bPunctureMap (R := K)).comp (algebraMap K (B (R := K))) =
      (overlapMap K).comp LaurentPolynomial.C := by
    ext r
    simp only [RingHom.comp_apply, overlapMap_C]
    exact (IsScalarTower.algebraMap_apply K K[X] (puncture K) r).symm
  rw [toTorus_eq_specMap]
  simpa only [bPuncture, bToBase, torusToBase, CommRingCat.ofHom_comp, Spec.map_comp]
    using congrArg (fun f : K →+* puncture K ↦ Spec.map (CommRingCat.ofHom f)) h

/-- The constructed scheme over the coefficient field. -/
def toBase : scheme K ⟶ Spec (.of K) :=
  pushout.desc (bToBase K) (torusToBase K) (overlap_toBase K)

@[reassoc (attr := simp)]
theorem node_toBase : node K ≫ toBase K = bToBase K := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_toBase : torus K ≫ toBase K = torusToBase K := pushout.inr_desc _ _ _

end OneGonGluing
end FLT.Mazur
