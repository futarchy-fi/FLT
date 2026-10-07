/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Etale.StandardEtale
/-! # Finite étale square-root covers

For a unit d, the standard étale square-root algebra is identified with
R[t]/(t²-d) when 2 is invertible. Its power basis proves finiteness and
rank two; the associated scheme map is an étale surjection. The
distinguished unit supplies the actual square root used in coordinate changes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Polynomial
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The monic equation adjoining a square root of a unit. -/
def quadraticRootPolynomial (d : Rˣ) : R[X] := X ^ 2 - C (d : R)

/-- The square-root equation is monic. -/
theorem quadraticRootPolynomial_monic (d : Rˣ) :
    (quadraticRootPolynomial d).Monic := monic_X_pow_sub_C _ (by decide)

/-- The square-root equation with its derivative inverted. -/
def quadraticEtalePair (d : Rˣ) : StandardEtalePair R where
  f := quadraticRootPolynomial d
  monic_f := quadraticRootPolynomial_monic d
  g := (quadraticRootPolynomial d).derivative
  cond := ⟨1, 0, 1, by simp⟩

/-- The ordinary monic square-root algebra. -/
abbrev QuadraticRootRing (d : Rˣ) := AdjoinRoot (quadraticRootPolynomial d)
/-- The standard étale square-root algebra. -/
abbrev QuadraticEtaleRing (d : Rˣ) := (quadraticEtalePair d).Ring

/-- The distinguished root squares to the original unit. -/
theorem quadraticRoot_square (d : Rˣ) :
    AdjoinRoot.root (quadraticRootPolynomial d) ^ 2 =
      algebraMap R (QuadraticRootRing d) (d : R) := by
  have h : aeval (AdjoinRoot.root (quadraticRootPolynomial d))
      (quadraticRootPolynomial d) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  change aeval (AdjoinRoot.root (quadraticRootPolynomial d)) (X ^ 2 - C (d : R)) = 0 at h
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

/-- The distinguished root of a unit is a unit. -/
theorem quadraticRoot_unit (d : Rˣ) :
    IsUnit (AdjoinRoot.root (quadraticRootPolynomial d)) := by
  have h : IsUnit (AdjoinRoot.root (quadraticRootPolynomial d) ^ 2) := by
    rw [quadraticRoot_square]
    exact d.isUnit.map (algebraMap R (QuadraticRootRing d))
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp h

/-- The derivative at the root is a unit when 2 is invertible. -/
theorem quadraticRoot_derivative_unit (d : Rˣ) (h2 : IsUnit (2 : R)) :
    IsUnit (aeval (AdjoinRoot.root (quadraticRootPolynomial d))
      (quadraticRootPolynomial d).derivative) := by
  have h2' := h2.map (algebraMap R (QuadraticRootRing d))
  have hd : (quadraticRootPolynomial d).derivative = 2 * X := by
    simp [quadraticRootPolynomial]
    ring
  rw [hd, map_mul, map_ofNat, aeval_X]
  simpa only [map_ofNat] using h2'.mul (quadraticRoot_unit d)

/-- The ordinary root algebra maps to the étale presentation. -/
def quadraticRootToEtale (d : Rˣ) :
    QuadraticRootRing d →ₐ[R] QuadraticEtaleRing d :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (quadraticEtalePair d).X
    (quadraticEtalePair d).hasMap_X.1

/-- The inverse map when 2 is invertible. -/
def quadraticEtaleToRoot (d : Rˣ) (h2 : IsUnit (2 : R)) :
    QuadraticEtaleRing d →ₐ[R] QuadraticRootRing d :=
  (quadraticEtalePair d).lift (AdjoinRoot.root (quadraticRootPolynomial d))
    ⟨by change aeval _ (quadraticRootPolynomial d) = 0
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], quadraticRoot_derivative_unit d h2⟩

/-- The étale presentation is the ordinary quadratic algebra. -/
def quadraticEtaleRootEquiv (d : Rˣ) (h2 : IsUnit (2 : R)) :
    QuadraticEtaleRing d ≃ₐ[R] QuadraticRootRing d :=
  AlgEquiv.ofAlgHom (quadraticEtaleToRoot d h2) (quadraticRootToEtale d)
    (by ext; simp only [quadraticEtaleToRoot, quadraticRootToEtale, AlgHom.comp_apply,
        AlgHom.id_apply, AdjoinRoot.liftAlgHom_root, StandardEtalePair.lift_X])
    (by
      apply (quadraticEtalePair d).hom_ext
      simp only [quadraticEtaleToRoot, quadraticRootToEtale, AlgHom.comp_apply,
        AlgHom.id_apply, AdjoinRoot.liftAlgHom_root, StandardEtalePair.lift_X])


/-- The transported power basis of the quadratic cover. -/
def quadraticEtaleBasis (d : Rˣ) (h2 : IsUnit (2 : R)) :
    Module.Basis (Fin (quadraticRootPolynomial d).natDegree) R (QuadraticEtaleRing d) :=
  (AdjoinRoot.powerBasis' (quadraticRootPolynomial_monic d)).basis.map
    (quadraticEtaleRootEquiv d h2).symm.toLinearEquiv

/-- The quadratic cover algebra is finite. -/
instance quadraticEtaleFinite (d : Rˣ) [Fact (IsUnit (2 : R))] :
    Module.Finite R (QuadraticEtaleRing d) :=
  Module.Finite.of_basis (quadraticEtaleBasis d Fact.out)

/-- The quadratic cover algebra is free. -/
instance quadraticEtaleFree (d : Rˣ) [Fact (IsUnit (2 : R))] :
    Module.Free R (QuadraticEtaleRing d) :=
  Module.Free.of_basis (quadraticEtaleBasis d Fact.out)

/-- The square-root equation has degree two. -/
theorem quadraticRootPolynomial_natDegree (d : Rˣ) [Nontrivial R] :
    (quadraticRootPolynomial d).natDegree = 2 := natDegree_X_pow_sub_C

/-- A monic quadratic algebra over a nontrivial ring is nontrivial. -/
instance quadraticRootNontrivial (d : Rˣ) [Nontrivial R] :
    Nontrivial (QuadraticRootRing d) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (quadraticRootPolynomial_monic d)).mpr
  rw [quadraticRootPolynomial, degree_X_pow_sub_C (by decide)]
  decide

/-- The étale quadratic algebra is nontrivial when 2 is invertible. -/
instance quadraticEtaleNontrivial (d : Rˣ) [Nontrivial R] [Fact (IsUnit (2 : R))] :
    Nontrivial (QuadraticEtaleRing d) :=
  (quadraticEtaleRootEquiv d Fact.out).toEquiv.nontrivial

/-- The cover algebra has rank two. -/
theorem quadraticEtale_finrank (d : Rˣ) [Nontrivial R] (h2 : IsUnit (2 : R)) :
    Module.finrank R (QuadraticEtaleRing d) = 2 := by
  have : Fact (IsUnit (2 : R)) := ⟨h2⟩
  rw [Module.finrank_eq_card_basis (quadraticEtaleBasis d h2), Fintype.card_fin,
    quadraticRootPolynomial_natDegree]

/-- The root in the standard étale presentation is a unit. -/
theorem quadraticEtale_root_unit (d : Rˣ) : IsUnit (quadraticEtalePair d).X := by
  have h := (quadraticRoot_unit d).map (quadraticRootToEtale d)
  simpa only [quadraticRootToEtale, AdjoinRoot.liftAlgHom_root] using h

/-- The distinguished square root as a unit. -/
def quadraticEtaleUnit (d : Rˣ) : (QuadraticEtaleRing d)ˣ :=
  (quadraticEtale_root_unit d).unit

/-- The distinguished unit satisfies the square-root equation. -/
theorem quadraticEtaleUnit_square (d : Rˣ) :
    (quadraticEtaleUnit d : QuadraticEtaleRing d) ^ 2 =
      algebraMap R (QuadraticEtaleRing d) (d : R) := by
  rw [quadraticEtaleUnit, IsUnit.unit_spec]
  have h := (quadraticEtalePair d).hasMap_X.1
  change aeval (quadraticEtalePair d).X (X ^ 2 - C (d : R)) = 0 at h
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

/-- The actual square-root covering morphism of schemes. -/
def quadraticEtaleCover (d : Rˣ) :
    Spec (.of (QuadraticEtaleRing d)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (QuadraticEtaleRing d)))

/-- The square-root cover is étale. -/
instance quadraticEtaleCoverEtale (d : Rˣ) : Etale (quadraticEtaleCover d) := by
  rw [quadraticEtaleCover, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The square-root cover is finite when 2 is invertible. -/
instance quadraticEtaleCoverFinite (d : Rˣ) [Fact (IsUnit (2 : R))] :
    IsFinite (quadraticEtaleCover d) := by
  rw [quadraticEtaleCover, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The square-root cover is surjective when 2 is invertible. -/
instance quadraticEtaleCoverSurjective (d : Rˣ) [Nontrivial R] [Fact (IsUnit (2 : R))] :
    Surjective (quadraticEtaleCover d) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap R (QuadraticEtaleRing d)))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := QuadraticEtaleRing d)

end WeierstrassCurve.CubicCharts
