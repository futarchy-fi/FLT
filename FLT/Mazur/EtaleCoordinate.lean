/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Étale coordinates of submersive presentations

The free coordinates of a submersive presentation give an étale map from a
polynomial algebra. In relative dimension one this is a map from `R[X]`.
The proof uses the Jacobi–Zariski sequence and the basis of differentials.
-/

@[expose] public section

open KaehlerDifferential
open scoped TensorProduct

namespace Algebra

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- An isomorphism on differentials kills the remaining cotangent terms. -/
theorem formallyEtale_of_bijective_mapBaseChange [Subsingleton (H1Cotangent R S)]
    (h : Function.Bijective (mapBaseChange R A S)) : FormallyEtale A S := by
  have hδ : H1Cotangent.δ R A S = 0 :=
    (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_δ_mapBaseChange R A S)).mp h.1
  have hδinj : Function.Injective (H1Cotangent.δ R A S) :=
    (LinearMap.injective_iff_eq_zero_of_exact
      (H1Cotangent.exact_map_δ R A S)).mpr (Subsingleton.elim _ _)
  have hmap : map R A S S = 0 :=
    (LinearMap.surjective_iff_eq_zero_of_exact (exact_mapBaseChange_map R A S)).mp h.2
  constructor
  · refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := map_surjective R A S x
    obtain ⟨y, rfl⟩ := map_surjective R A S y
    simp [hmap]
  · exact ⟨fun x y ↦ hδinj (by simp [hδ])⟩

/-- A polynomial coordinate system whose differentials form a basis is étale. -/
theorem etale_mvPolynomial_of_basis {κ : Type*} [Finite κ]
    [FinitePresentation R S] [Subsingleton (H1Cotangent R S)]
    (v : κ → S) (b : Module.Basis κ S Ω[S⁄R]) (hb : ∀ i, b i = D R S (v i)) :
    (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  let := (MvPolynomial.aeval (R := R) v).toAlgebra
  have : IsScalarTower R (MvPolynomial κ R) S :=
    IsScalarTower.of_algebraMap_eq' (MvPolynomial.aeval (R := R) v).comp_algebraMap.symm
  let b' := (mvPolynomialBasis R κ).baseChange S
  have heq : mapBaseChange R (MvPolynomial κ R) S =
      (b'.equiv b (Equiv.refl κ)).toLinearMap := by
    apply b'.ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [b', Module.Basis.baseChange_apply, mvPolynomialBasis_apply,
      mapBaseChange_tmul, map_D, one_smul, Equiv.refl_apply, hb]
    change D R S ((MvPolynomial.aeval (R := R) v) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  have : FormallyEtale (MvPolynomial κ R) S :=
    formallyEtale_of_bijective_mapBaseChange (R := R) (by
      rw [heq]
      exact (b'.equiv b (Equiv.refl κ)).bijective)
  exact ⟨inferInstance, FinitePresentation.of_restrict_scalars_finitePresentation R _ _⟩

end Algebra

namespace Algebra.SubmersivePresentation

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Finite σ] (P : SubmersivePresentation R S ι σ)

/-- Indices of the coordinates outside the invertible Jacobian minor. -/
abbrev FreeCoordinates := ((Set.range P.map)ᶜ : Set ι)

/-- The polynomial map given by the free coordinates of the presentation. -/
noncomputable def freeCoordinateHom : MvPolynomial P.FreeCoordinates R →ₐ[R] S :=
  MvPolynomial.aeval fun i ↦ P.val i

@[simp]
theorem freeCoordinateHom_X (i : P.FreeCoordinates) :
    P.freeCoordinateHom (MvPolynomial.X i) = P.val i := by
  simp [freeCoordinateHom]

/-- The free-coordinate polynomial map of a finite submersive presentation is étale. -/
theorem freeCoordinateHom_etale [Finite ι] : P.freeCoordinateHom.toRingHom.Etale := by
  have := P.isStandardSmooth
  exact etale_mvPolynomial_of_basis (fun i : P.FreeCoordinates ↦ P.val i)
    P.basisKaehler P.basisKaehler_apply

variable [Finite ι]

/-- The free-coordinate count agrees with the relative dimension. -/
theorem card_freeCoordinates : Nat.card P.FreeCoordinates = P.dimension := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  simp only [FreeCoordinates, Nat.card_eq_fintype_card, Fintype.card_compl_set,
    Set.card_range_of_injective P.map_inj, Presentation.dimension]

/-- A relative-dimension-one presentation has a unique free coordinate. -/
@[instance_reducible]
noncomputable def uniqueFreeCoordinate (h : P.dimension = 1) : Unique P.FreeCoordinates := by
  have hc : Nat.card P.FreeCoordinates = 1 := P.card_freeCoordinates.trans h
  let hx := Nat.card_eq_one_iff_exists.mp hc
  exact ⟨⟨Classical.choose hx⟩, Classical.choose_spec hx⟩

/-- The unique free coordinate, viewed as an element of the presented algebra. -/
noncomputable def coordinate (h : P.dimension = 1) : S :=
  P.val (P.uniqueFreeCoordinate h).default

/-- Every free-coordinate index selects the same element in relative dimension one. -/
theorem coordinate_eq (h : P.dimension = 1) (i : P.FreeCoordinates) :
    P.coordinate h = P.val i := by
  have hi := (P.uniqueFreeCoordinate h).uniq i
  exact congrArg (fun j : P.FreeCoordinates ↦ P.val j) hi.symm

/-- The univariate polynomial map attached to a dimension-one presentation. -/
noncomputable def coordinateHom (h : P.dimension = 1) : Polynomial R →ₐ[R] S :=
  Polynomial.aeval (P.coordinate h)

@[simp]
theorem coordinateHom_X (h : P.dimension = 1) :
    P.coordinateHom h Polynomial.X = P.coordinate h := by
  simp [coordinateHom]

/-- The coordinate map is the free-coordinate map after identifying its variable with `X`. -/
theorem coordinateHom_eq (h : P.dimension = 1) :
    let := P.uniqueFreeCoordinate h
    P.coordinateHom h = P.freeCoordinateHom.comp
      (MvPolynomial.uniqueAlgEquiv R P.FreeCoordinates).symm.toAlgHom := by
  let := P.uniqueFreeCoordinate h
  ext
  simp [coordinateHom, coordinate, freeCoordinateHom,
    MvPolynomial.uniqueAlgEquiv_symm_apply]

/-- The unique free coordinate of a dimension-one submersive presentation is étale. -/
theorem coordinateHom_etale (h : P.dimension = 1) : (P.coordinateHom h).toRingHom.Etale := by
  let := P.uniqueFreeCoordinate h
  rw [P.coordinateHom_eq h]
  let e := (MvPolynomial.uniqueAlgEquiv R P.FreeCoordinates).symm
  have hf := P.freeCoordinateHom_etale
  algebraize [e.toRingHom, P.freeCoordinateHom.toRingHom,
    P.freeCoordinateHom.toRingHom.comp e.toRingHom]
  have : Etale (Polynomial R) (MvPolynomial P.FreeCoordinates R) :=
    RingHom.Etale.of_bijective e.bijective
  exact Etale.comp (Polynomial R) (MvPolynomial P.FreeCoordinates R) S

end Algebra.SubmersivePresentation
