/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAlgebraicPointDescent
public import FLT.Mazur.GeometricPicardSheafRepresentative
public import FLT.Mazur.SmoothTranslationGeometricClass

/-!
# Finite coefficient descent of arbitrary algebraic geometric Picard classes

Represent the original geometric sheaf section by an actual line, recover
that line in an original smooth ordered parameter scheme, and descend its
whole parameter point through a finite residue-field extension. The input
class is arbitrary; its finite coefficient descent is a conclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open SchemePicard FCurve OrderedCurvePower OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R]
  [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B) (t : Spec (.of k) ⟶ Spec (.of R))

include hB in
/-- Every original Picard section over an algebraic closure descends to finite coefficients. -/
theorem exists_finite_picard_descent
    (s : (relativeFppfSheaf f).obj.obj (op (coefficientTest (K := K) t))) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (i : L →ₐ[k] K) (s₀ : (relativeFppfSheaf f).obj.obj
        (op (coefficientTest (K := L) t))),
      (relativeFppfSheaf f).obj.map (restriction t i).op s₀ = s := by
  obtain ⟨M, hM⟩ := exists_geometric_picardSheaf_line f (coefficientTest (K := K) t).hom s
  obtain ⟨j, p, hp⟩ := exists_smoothTranslation_geometric_class f hB
    (coefficientTest (K := K) t).hom M
  obtain ⟨L, hL, hA, hfin, i, q, hq⟩ :=
    OriginalAlgebraicPointDescent.exists_finite_original_factor t p
  let _ := hL
  let _ := hA
  let _ := hfin
  refine ⟨L, hL, hA, hfin, i,
    (relativeFppfSheaf f).obj.map q.op (smoothTranslationClass f hB.2.1 j), ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hq]
  exact hp.trans hM

end FLT.Mazur.HilbertChart
