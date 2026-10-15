/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFiberFiniteSectionOrbit
public import FLT.Mazur.AcyclicDegreeOpenAutomorphism
public import FLT.Mazur.GeometricAcyclicOrbitTranslation

/-!
# Original acyclic translations from finite coefficient descent

Finite coefficient descent of the geometric input proves finite orbit of
the actual acyclic degree open. Combined with geometric irreducibility,
this constructs an original affine étale translation valid at every
independent original lift of the same input class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard OriginalFiniteCoefficientOrbit OriginalFiberFiniteSectionOrbit
set_option backward.isDefEq.respectTransparency false
variable {R k L K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Module.Finite k L]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  (t : Spec (.of k) ⟶ Spec (.of R)) (i : L →ₐ[k] K)
  {V Y : Over (Spec (.of R))}
  (a : Y ⟶ V) (b : Y ⟶ coefficientTest (K := K) t)
  (H : IsPullback a.left b.left V.hom (coefficientTest (K := K) t).hom)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (s₀ : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := L) t))) (d : ℕ)

/-- Finite coefficient descent proves the previously explicit acyclic-open orbit premise. -/
theorem acyclicDegreeOpen_finite_of_descent :
    (Set.range (fun σ : K ≃ₐ[k] K ↦
      (ResidueGeometricConjugacy.fiberAction t H σ).hom ⁻¹'
        (unpointedAcyclicDegreeOpen f Y
          ((relativeFppfSheaf f).obj.map b.op
            ((relativeFppfSheaf f).obj.map (restriction t i).op s₀) *
              (relativeFppfSheaf f).obj.map a.op c) d : Set Y.left))).Finite :=
  acyclicDegreeOpen_finite_orbit f (fiberIso t a b H) _ d
    (finite_translated_section_orbit t a b H (relativeFppfSheaf f).obj i s₀ c)

include H in
/-- Every independent original lift works for a geometric class with finite coefficient descent. -/
theorem exists_all_independent_acyclic_translation_of_descent
    [IsAlgClosed K] [Algebra.IsAlgebraic k K] [IsPreimmersion t]
    [Smooth V.hom] [IrreducibleSpace Y.left]
    (hne : (unpointedAcyclicDegreeOpen f Y
      ((relativeFppfSheaf f).obj.map b.op
        ((relativeFppfSheaf f).obj.map (restriction t i).op s₀) *
          (relativeFppfSheaf f).obj.map a.op c) d : Set Y.left).Nonempty) :
    ∃ (E : Over (Spec (.of R))) (r : E ⟶ V)
      (_z : coefficientTest (K := K) t ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : coefficientTest (K := K) t ⟶ E,
        (relativeFppfSheaf f).obj.map (restriction t i).op s₀ *
          (relativeFppfSheaf f).obj.map w.op ((relativeFppfSheaf f).obj.map r.op c) ∈
            (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) :=
  exists_all_independent_acyclic_translation f t d a b H c _ hne
    (acyclicDegreeOpen_finite_of_descent f t i a b H c s₀ d)

end FLT.Mazur.HilbertChart
