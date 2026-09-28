/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The projective line from its two affine charts

Glue two copies of `Spec K[X]` along the Laurent polynomial spectrum. The first
map sends `X` to `T 1`; the second sends it to `T (-1)`. The scheme is the
pushout of these specific open immersions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial LaurentPolynomial

universe u

namespace FLT.Mazur.ProjectiveLine

variable (K : Type u) [Field K]

/-- The affine coordinate chart. -/
abbrev chart := Spec (CommRingCat.of K[X])

/-- The intersection of the two charts. -/
abbrev overlap := Spec (CommRingCat.of K[T;T⁻¹])

/-- The standard inclusion of the punctured affine line. -/
def overlapLeft : overlap K ⟶ chart K :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : K[X] →+* K[T;T⁻¹]))

instance : IsOpenImmersion (overlapLeft K) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : K[X])

/-- Inversion of the Laurent coordinate on the overlap. -/
def inversion : overlap K ≅ overlap K :=
  Scheme.Spec.mapIso (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.op)

@[simp]
theorem inversion_hom : (inversion K).hom =
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingHom) := by
  rfl

/-- The inclusion into the second chart, using the inverse coordinate. -/
def overlapRight : overlap K ⟶ chart K :=
  (inversion K).hom ≫ overlapLeft K

instance : IsOpenImmersion (overlapRight K) := by
  unfold overlapRight
  infer_instance

/-- The transition sends the affine coordinate to its Laurent inverse. -/
theorem transition_X :
    LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X : K[X])) =
      LaurentPolynomial.T (-1) := by
  simp

/-- The fixed projective line obtained by gluing the two coordinate charts. -/
def scheme : Scheme.{u} := pushout (overlapLeft K) (overlapRight K)

/-- The first affine chart of the projective line. -/
def left : chart K ⟶ scheme K := pushout.inl _ _

/-- The second affine chart of the projective line. -/
def right : chart K ⟶ scheme K := pushout.inr _ _

instance : IsOpenImmersion (left K) := by
  change IsOpenImmersion (colimit.ι (span (overlapLeft K) (overlapRight K))
    WalkingSpan.left)
  infer_instance

instance : IsOpenImmersion (right K) := by
  change IsOpenImmersion (colimit.ι (span (overlapLeft K) (overlapRight K))
    WalkingSpan.right)
  infer_instance

/-- The chart maps agree along the specified inverse-coordinate transition. -/
theorem overlap_condition : overlapLeft K ≫ left K = overlapRight K ≫ right K :=
  pushout.condition

/-- Every point belongs to one of the two affine charts. -/
theorem charts_cover (x : scheme K) :
    (∃ y : chart K, left K y = x) ∨ ∃ y : chart K, right K y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (overlapLeft K) (overlapRight K)) x
  cases i with
  | none =>
    left
    refine ⟨overlapLeft K y, ?_⟩
    change (overlapLeft K ≫ left K) y = x
    rw [show overlapLeft K ≫ left K =
      colimit.ι (span (overlapLeft K) (overlapRight K)) WalkingSpan.zero from
        colimit.w (span (overlapLeft K) (overlapRight K)) WalkingSpan.Hom.fst]
    exact hy
  | some i =>
    cases i with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

/-- The structure morphism of either affine chart. -/
def chartToBase : chart K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

theorem overlap_toBase :
    overlapLeft K ≫ chartToBase K = overlapRight K ≫ chartToBase K := by
  have h : (Polynomial.toLaurent : K[X] →+* K[T;T⁻¹]).comp Polynomial.C =
      LaurentPolynomial.invert.toRingHom.comp
        ((Polynomial.toLaurent : K[X] →+* K[T;T⁻¹]).comp Polynomial.C) := by
    ext x
    simp
  rw [overlapRight, Category.assoc, inversion_hom]
  have hh := congrArg (fun f : K →+* K[T;T⁻¹] ↦ Spec.map (CommRingCat.ofHom f)) h
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    overlapLeft, chartToBase] using hh

/-- The structure morphism of the glued projective line. -/
def toBase : scheme K ⟶ Spec (CommRingCat.of K) :=
  pushout.desc (chartToBase K) (chartToBase K) (overlap_toBase K)

@[reassoc (attr := simp)]
theorem left_toBase : left K ≫ toBase K = chartToBase K :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_toBase : right K ≫ toBase K = chartToBase K :=
  pushout.inr_desc _ _ _

end FLT.Mazur.ProjectiveLine
