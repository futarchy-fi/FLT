/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicPicardFiniteDescent
public import FLT.Mazur.GeometricAcyclicFiniteDescent

/-!
# All-independent-lift translations for arbitrary algebraic geometric classes

Finite coefficient descent and the finite orbit of the actual acyclic open
are proved for the arbitrary input class. Only geometric nonemptiness and
irreducibility of the chosen translation fiber are retained as premises.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  (t : Spec (.of k) ⟶ Spec (.of R))
  {V Y : Over (Spec (.of R))}
  (a : Y ⟶ V) (b : Y ⟶ coefficientTest (K := K) t)
  (H : IsPullback a.left b.left V.hom (coefficientTest (K := K) t).hom)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t))) (d : ℕ)

include hB in
/-- The actual acyclic degree open of every algebraic geometric Picard class has finite orbit. -/
theorem acyclicDegreeOpen_finite_algebraic_orbit :
    (Set.range (fun σ : K ≃ₐ[k] K ↦
      (ResidueGeometricConjugacy.fiberAction t H σ).hom ⁻¹'
        (unpointedAcyclicDegreeOpen f Y
          ((relativeFppfSheaf f).obj.map b.op s *
            (relativeFppfSheaf f).obj.map a.op c) d : Set Y.left))).Finite := by
  obtain ⟨L, hL, hA, hfin, i, s₀, hs⟩ := exists_finite_picard_descent f hB t s
  let _ := hL
  let _ := hA
  let _ := hfin
  simpa only [hs] using acyclicDegreeOpen_finite_of_descent f t i a b H c s₀ d

include hB H in
/-- No finite-orbit or coefficient-descent premise is needed for algebraic geometric inputs. -/
theorem exists_all_independent_acyclic_translation_algebraic
    [IsPreimmersion t] [Smooth V.hom] [IrreducibleSpace Y.left]
    (hne : (unpointedAcyclicDegreeOpen f Y
      ((relativeFppfSheaf f).obj.map b.op s *
        (relativeFppfSheaf f).obj.map a.op c) d : Set Y.left).Nonempty) :
    ∃ (E : Over (Spec (.of R))) (r : E ⟶ V) (_z : coefficientTest (K := K) t ⟶ E),
      IsAffine E.left ∧ Etale E.hom ∧
      ∀ w : coefficientTest (K := K) t ⟶ E,
        s * (relativeFppfSheaf f).obj.map w.op ((relativeFppfSheaf f).obj.map r.op c) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (coefficientTest (K := K) t)) :=
  exists_all_independent_acyclic_translation f t d a b H c s hne
    (acyclicDegreeOpen_finite_algebraic_orbit f hB t a b H c s d)

end FLT.Mazur.HilbertChart
