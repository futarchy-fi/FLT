/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Closed polynomial embeddings of finite-type affine schemes

An affine scheme of finite type over an affine base embeds as a closed subscheme
of the spectrum of a polynomial algebra in finitely many variables over that
base. The embedding and its compatibility with the original structure map are
constructed from finite generation. This is the affine part of the projective
chart embedding needed by Stacks 0200; no projective embedding is asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace FLT.Mazur.Chow

/-- A finite-type affine scheme over `Spec R` has a closed polynomial embedding
which commutes with its given structure morphism. -/
theorem exists_closed_polynomial_embedding {X : Scheme.{u}} [IsAffine X]
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (j : X ⟶ Spec (.of (MvPolynomial (Fin n) R))),
      IsClosedImmersion j ∧
        j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* _)) = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hfinite : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hring : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfinite
  let _sectionAlgebra := φ.hom.toAlgebra
  have _sectionFiniteType : Algebra.FiniteType R Γ(X, ⊤) := hring
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    _sectionFiniteType
  let j : X ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom q.toRingHom)
  have _polynomialClosed : IsClosedImmersion (Spec.map (CommRingCat.ofHom q.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  refine ⟨n, j, inferInstance, ?_⟩
  have hcomp : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) ≫
      CommRingCat.ofHom q.toRingHom = φ := by
    ext r
    exact q.commutes r
  dsimp only [j]
  rw [Category.assoc, ← Spec.map_comp, hcomp, hφ, Iso.hom_inv_id_assoc]

end FLT.Mazur.Chow
