/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionQuotient
public import Mathlib.Algebra.Polynomial.OfFn
/-! # Field-valued fibers of the scalar quotient

The actual quotient map identifies exactly scalar orbits on field-valued
points. The orbit separation argument uses an orbit polynomial and does not
require the scalar group order to be invertible. Surjectivity on rational
points over a general field is not asserted.
-/

open Polynomial
open AlgebraicGeometry CategoryTheory Opposite
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
/-- Invariant coordinates separate finite-group orbits of domain-valued points. -/
theorem invariantPoint_orbit
    {G A K : Type*} [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
    [CommRing K] [IsDomain K] (f g : A →+* K)
    (hfg : ∀ a : A, (∀ σ : G, σ • a = a) → f a = g a) :
    ∃ σ : G, ∀ a : A, f a = g (σ • a) := by
  classical
  let := Fintype.ofFinite G
  by_contra! h
  choose a ha using h
  let e := Fintype.equivFin G
  let P : A[X] := Polynomial.ofFn (Fintype.card G) (fun i => a (e.symm i))
  let Q := MulSemiringAction.charpoly G P
  have hmap : Q.map (Polynomial.mapRingHom f) = Q.map (Polynomial.mapRingHom g) := by
    ext i j
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    apply hfg
    intro σ
    have hs := MulSemiringAction.smul_coeff_charpoly (G := G) P i σ
    simpa only [Polynomial.coeff_smul] using
      congrArg (fun p : A[X] => p.coeff j) hs
  have hroot : (Q.map (Polynomial.mapRingHom f)).eval (P.map f) = 0 := by
    simp only [Q, MulSemiringAction.charpoly, Polynomial.map_prod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
    simp
  rw [hmap] at hroot
  have hp : ∏ σ : G, (P.map f - (σ • P).map g) = 0 := by
    simpa [Q, MulSemiringAction.charpoly, Polynomial.map_prod,
      Polynomial.eval_prod, Polynomial.coe_mapRingHom] using hroot
  obtain ⟨σ, _, hσ⟩ := Finset.prod_eq_zero_iff.mp hp
  have hc := congrArg (fun p : K[X] => p.coeff (e σ).val) (sub_eq_zero.mp hσ)
  apply ha σ
  simpa only [Polynomial.coeff_map, Polynomial.coeff_smul, P,
    Polynomial.ofFn_coeff_eq_val_of_lt _ (e σ).isLt, e.symm_apply_apply] using hc

universe u
variable {R : Type u} [CommRing R]

/-- Algebra maps are points of the affine spectrum over the base. -/
def specAlgPointEquiv (A K : Type u) [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] :
    (A →ₐ[R] K) ≃ ((algSpec (.of R)).obj (op (CommAlgCat.of R K)) ⟶
      (algSpec (.of R)).obj (op (CommAlgCat.of R A))) where
  toFun f := (algSpec (.of R)).map (CommAlgCat.ofHom f).op
  invFun p := ((algSpec.fullyFaithful (R := .of R)).preimage p).unop.hom
  left_inv f := by simp
  right_inv p := by
    exact (algSpec.fullyFaithful (R := .of R)).map_preimage p

variable [IsNoetherianRing R] [IsDomain R] (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- Equality on scalar invariants is equivalent to a scalar orbit relation. -/
theorem scalarInvariantPoint_fiber (K : Type u) [Field K] [Algebra R K]
    (f g : NonzeroTorsionRing W n →ₐ[R] K) :
    f.comp (TorsionScalarInvariantRing W n).val =
      g.comp (TorsionScalarInvariantRing W n).val ↔
      ∃ σ : (ZMod n)ˣ, f = g.comp (nonzeroTorsionRingScalar W n σ).toAlgHom := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := invariantPoint_orbit f.toRingHom g.toRingHom
      (fun a ha => AlgHom.congr_fun h ⟨a, ha⟩)
    exact ⟨σ, AlgHom.ext hσ⟩
  · rintro ⟨σ, rfl⟩
    ext a
    exact congrArg g (a.property σ)


/-- Coordinate points are actual points of the nonzero torsion scheme. -/
def nonzeroTorsionCoordinatePointEquiv (K : Type u) [Field K] [Algebra R K] :
    (NonzeroTorsionRing W n →ₐ[R] K) ≃
      (pointSource K ⟶ nonzeroTorsionModel W n) := by
  let e : nonzeroTorsionModel W n ≅
      (algSpec (.of R)).obj (op (CommAlgCat.of R (NonzeroTorsionRing W n))) :=
    (nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))
  change (NonzeroTorsionRing W n →ₐ[R] K) ≃
    ((algSpec (.of R)).obj (op (CommAlgCat.of R K)) ⟶ nonzeroTorsionModel W n)
  exact (specAlgPointEquiv (NonzeroTorsionRing W n) K).trans
    { toFun := fun p => p ≫ e.inv
      invFun := fun p => p ≫ e.hom
      left_inv := fun p => by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      right_inv := fun p => by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] }

/-- The coordinate scalar action corresponds to inverse pullback on scheme points. -/
theorem nonzeroTorsionCoordinatePoint_scalar (K : Type u) [Field K] [Algebra R K]
    (f : NonzeroTorsionRing W n →ₐ[R] K) (σ : (ZMod n)ˣ) :
    nonzeroTorsionCoordinatePointEquiv W n K
      (f.comp (nonzeroTorsionRingScalar W n σ).toAlgHom) =
    nonzeroTorsionCoordinatePointEquiv W n K f ≫
      (nonzeroTorsionScalarAction W n σ).inv := by
  let A := NonzeroTorsionRing W n
  let e : nonzeroTorsionModel W n ≅
      (algSpec (.of R)).obj (op (CommAlgCat.of R A)) :=
    (nonzeroTorsionModel W n).left.isoSpec.asOver (Spec (.of R))
  have ha : (algSpec (.of R)).map
      (CommAlgCat.ofHom (nonzeroTorsionRingScalar W n σ).toAlgHom).op =
      e.inv ≫ (nonzeroTorsionScalarAction W n σ).inv ≫ e.hom :=
    affineCoordinateAut_spec A (nonzeroTorsionModel W n) e
      (nonzeroTorsionScalarAction W n σ)
  have hc : specAlgPointEquiv A K
      (f.comp (nonzeroTorsionRingScalar W n σ).toAlgHom) =
      specAlgPointEquiv A K f ≫ (algSpec (.of R)).map
        (CommAlgCat.ofHom (nonzeroTorsionRingScalar W n σ).toAlgHom).op := by
    exact (algSpec (.of R)).map_comp (CommAlgCat.ofHom f).op
      (CommAlgCat.ofHom (nonzeroTorsionRingScalar W n σ).toAlgHom).op
  rw [ha] at hc
  change _ ≫ e.inv = (_ ≫ e.inv) ≫ _
  rw [hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The quotient map on points is restriction to the invariant coordinates. -/
theorem nonzeroTorsionCoordinatePoint_quotient (K : Type u) [Field K] [Algebra R K]
    (f : NonzeroTorsionRing W n →ₐ[R] K) :
    (nonzeroTorsionCoordinatePointEquiv W n K f ≫ scalarQuotientMap W n).left =
      Spec.map (CommRingCat.ofHom
        (f.comp (TorsionScalarInvariantRing W n).val).toRingHom) := by
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (nonzeroTorsionModel W n).left.isoSpec.inv) ≫
      ((nonzeroTorsionModel W n).left.isoSpec.hom ≫ _) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Spec.map_comp _ _).symm


/-- Fibers of the actual scalar quotient on field-valued points are exactly scalar orbits. -/
theorem scalarQuotientFieldPoint_fiber (K : Type u) [Field K] [Algebra R K]
    (p q : pointSource K ⟶ nonzeroTorsionModel W n) :
    p ≫ scalarQuotientMap W n = q ≫ scalarQuotientMap W n ↔
      ∃ σ : (ZMod n)ˣ, p = q ≫ (nonzeroTorsionScalarAction W n σ).inv := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := (nonzeroTorsionCoordinatePointEquiv W n K).surjective p
    obtain ⟨g, rfl⟩ := (nonzeroTorsionCoordinatePointEquiv W n K).surjective q
    have h' := congrArg Over.Hom.left h
    rw [nonzeroTorsionCoordinatePoint_quotient,
      nonzeroTorsionCoordinatePoint_quotient] at h'
    have hf : f.comp (TorsionScalarInvariantRing W n).val =
        g.comp (TorsionScalarInvariantRing W n).val := by
      apply AlgHom.coe_ringHom_injective
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')
    obtain ⟨σ, rfl⟩ := (scalarInvariantPoint_fiber W n K f g).mp hf
    exact ⟨σ, nonzeroTorsionCoordinatePoint_scalar W n K g σ⟩
  · rintro ⟨σ, rfl⟩
    rw [Category.assoc, scalarQuotientMap_invariant_inv]

end WeierstrassCurve.CubicCharts
