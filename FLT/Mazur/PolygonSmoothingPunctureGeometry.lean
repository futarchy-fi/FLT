/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureCalculus
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Geometric squares for the complete puncture substitutions

The algebraic composition convention becomes the contravariant spectrum
square. Equal smoothing identifications preserve both full puncture arrows.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false

/-- The original full puncture selected by its node coordinate. -/
def punctureOpen (t : R) (b : Bool) : Spec (.of R[T;T⁻¹]) ⟶ chart R t :=
  Spec.map (CommRingCat.ofHom (punctureLaurentMap t b).toRingHom)

/-- The positive label is the original left branch arrow. -/
theorem punctureOpen_true (t : R) : punctureOpen t true = leftBranchOpen R t :=
  (leftBranchOpen_eq_spec R t).symm

/-- The negative label is the original right branch with its own positive coordinate. -/
theorem punctureOpen_false (t : R) : punctureOpen t false = rightBranchOpen R t :=
  (rightBranchOpen_eq_spec t).symm

/-- The actual Laurent scheme automorphism induced by a full algebra equivalence. -/
def punctureSpecIso (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) :
    Spec (.of R[T;T⁻¹]) ≅ Spec (.of R[T;T⁻¹]) :=
  Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.op

/-- A complete ring factorization gives the geometric puncture square in the correct order. -/
@[reassoc] theorem punctureFactor_spec (s t : R) (f : ChartRing s ≃ₐ[R] ChartRing t)
    (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap s b)) :
    punctureOpen t b ≫ (Scheme.Spec.mapIso f.toRingEquiv.toCommRingCatIso.op).hom =
      (punctureSpecIso a).hom ≫ punctureOpen s b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hf))

/-- Equal smoothing identifications leave each original full puncture unchanged. -/
@[reassoc] theorem punctureOpen_parameter (s t : R) (h : s = t) (b : Bool) :
    punctureOpen s b ≫ (nodeParameterIso s t h).hom = punctureOpen t b := by
  subst t
  simp only [nodeParameterIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- A normalized source correction retains its full puncture substitution. -/
@[reassoc] theorem punctureFactor_spec_normalized (s t : R) (h : s = t)
    (f : ChartRing s ≃ₐ[R] ChartRing t) (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap s b)) :
    punctureOpen t b ≫
        (Scheme.Spec.mapIso f.toRingEquiv.toCommRingCatIso.op ≪≫ nodeParameterIso s t h).hom =
      (punctureSpecIso a).hom ≫ punctureOpen t b := by
  rw [Iso.trans_hom, ← Category.assoc, punctureFactor_spec s t f a b hf,
    Category.assoc, punctureOpen_parameter]

end FLT.Mazur.PolygonSmoothing
