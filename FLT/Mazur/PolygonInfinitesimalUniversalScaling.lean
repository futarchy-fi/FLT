/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalScalingNaturality
public import FLT.Mazur.PolygonParameterProjectionComposition

/-!
# A variable scaling parameter on the whole original infinitesimal polygon

The universal Laurent parameter acts on the entire original polygon after
coefficient extension. Specialization recovers every full coefficient-unit
automorphism, including all nilpotents and original node charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The smoothing parameter remains nilpotent over the universal parameter ring. -/
instance laurentParameter_nilpotent : Fact (IsNilpotent (LaurentPolynomial.C t : R[T;T⁻¹])) :=
  ⟨(Fact.out : IsNilpotent t).map LaurentPolynomial.C⟩

/-- The actual full family with a variable invertible scaling parameter. -/
abbrev scalingParameterFamily := scheme R[T;T⁻¹] (LaurentPolynomial.C t) n h

/-- Forget the variable scaling parameter without changing the original polygon. -/
def scalingParameterProjection : scalingParameterFamily R t n h ⟶ scheme R t n h :=
  parameterProjection LaurentPolynomial.C t (LaurentPolynomial.C t) rfl n h

/-- A variable parameter gives a morphism into the entire original infinitesimal polygon. -/
def universalScaling : scalingParameterFamily R t n h ⟶ scheme R t n h :=
  scaling R[T;T⁻¹] (LaurentPolynomial.C t) n h (PolygonUniversalScaling.u (R := R)) ≫
    scalingParameterProjection R t n h

/-- Each original full node chart carries exactly the universal reciprocal-coordinate map. -/
@[reassoc] theorem chart_universalScaling (i : Fin n) :
    chart R[T;T⁻¹] (LaurentPolynomial.C t) n h i ≫ universalScaling R t n h =
      Spec.map (CommRingCat.ofHom (universalReciprocalScale t)) ≫ chart R t n h i := by
  rw [universalScaling, chart_scaling_assoc, scalingParameterProjection,
    chart_parameterProjection, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The variable action retains the original arithmetic structure morphism. -/
@[reassoc] theorem universalScaling_base :
    universalScaling R t n h ≫ toBase R t n h =
      toBase R[T;T⁻¹] (LaurentPolynomial.C t) n h ≫
        Spec.map (CommRingCat.ofHom LaurentPolynomial.C) := by
  rw [universalScaling, Category.assoc, scalingParameterProjection,
    parameterProjection_base, scaling_toBase_assoc]

/-- Substitute an arbitrary original coefficient unit for the variable parameter. -/
def scalingParameterSection (a : Rˣ) : scheme R t n h ⟶ scalingParameterFamily R t n h :=
  parameterProjection (LaurentPolynomial.eval₂ (RingHom.id R) a)
    (LaurentPolynomial.C t) t (by simp) n h

/-- Substitution leaves the original full polygon unchanged under parameter projection. -/
@[reassoc] theorem scalingParameterSection_projection (a : Rˣ) :
    scalingParameterSection R t n h a ≫ scalingParameterProjection R t n h = 𝟙 _ := by
  rw [scalingParameterSection, scalingParameterProjection, parameterProjection_comp]
  have he : (LaurentPolynomial.eval₂ (RingHom.id R) a).comp LaurentPolynomial.C =
      RingHom.id R := by ext r; simp
  simpa only [he] using parameterProjection_id t n h

/-- Specialization of the variable action recovers the full original automorphism. -/
@[reassoc] theorem scalingParameterSection_universalScaling (a : Rˣ) :
    scalingParameterSection R t n h a ≫ universalScaling R t n h = scaling R t n h a := by
  have hu : Units.map (LaurentPolynomial.eval₂ (RingHom.id R) a)
      (PolygonUniversalScaling.u (R := R)) = a := by
    ext
    exact PolygonUniversalScaling.specialize_u a
  rw [universalScaling, ← Category.assoc]
  rw [show scalingParameterSection R t n h a ≫
      scaling R[T;T⁻¹] (LaurentPolynomial.C t) n h (PolygonUniversalScaling.u (R := R)) =
      scaling R t n h a ≫ scalingParameterSection R t n h a from by
    simpa only [hu, scalingParameterSection] using
      (scaling_parameterProjection (LaurentPolynomial.eval₂ (RingHom.id R) a)
        (LaurentPolynomial.C t) t (by simp) n h (PolygonUniversalScaling.u (R := R))).symm]
  rw [Category.assoc, scalingParameterSection_projection, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimal
