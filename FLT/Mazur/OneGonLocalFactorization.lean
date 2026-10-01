/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonNodeFiber

/-!
# Affine target factorizations near the pinched point

For an arbitrary scheme target, a normalization map taking zero and one to
the same point factors through an affine open after restriction to a
principal neighborhood containing both endpoints. The neighborhood is
constructed using closedness of the finite normalization map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open FLT.Mazur.PolygonNodePresentation FLT.Mazur.OneGonPinchingAlgebra
open FLT.Mazur.OneGonNodeFiber

namespace FLT.Mazur.OneGonLocalFactorization

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- An affine target open contains the image of a whole principal normalization neighborhood. -/
theorem exists_principal_affine_neighborhood
    (f : Spec (.of K[X]) ⟶ X) (hf : f (endpoint 0) = f (endpoint 1)) :
    ∃ (s : B (R := K)), bEval s ≠ 0 ∧
      ∃ U : X.Opens, IsAffineOpen U ∧
        ∀ p : PrimeSpectrum K[X], p ∈ PrimeSpectrum.basicOpen s.val → f p ∈ U := by
  obtain ⟨U, hU, h0, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := f (endpoint 0)) (U := ⊤) (by trivial)
  let V : (Spec (.of (B (R := K)))).Opens :=
    ⟨(toPinching '' (f ⁻¹' (U : Set X))ᶜ)ᶜ,
      (toPinching_isClosedMap _ (U.isOpen.preimage f.continuous).isClosed_compl).isOpen_compl⟩
  have hn : nodePoint (K := K) ∈ V := by
    rintro ⟨p, hp, hpn⟩
    apply hp
    rcases (fiber_node p).mp hpn with rfl | rfl
    · exact h0
    · exact (congrArg (fun x : X ↦ x ∈ U) hf).mp h0
  obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B (R := K))).exists_subset_of_mem_open
      hn V.isOpen
  refine ⟨s, hs, U, hU, ?_⟩
  intro p hp
  by_contra hbad
  have hps : toPinching p ∈ PrimeSpectrum.basicOpen s := hp
  exact hsub hps ⟨p, hbad, rfl⟩

/-- The principal normalization chart maps to the original affine line. -/
def lineInclusion (s : B (R := K)) :
    Spec (.of (OneGonLocalizedPinching.line s)) ⟶ Spec (.of K[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (OneGonLocalizedPinching.line s)))

/-- Its image is the principal open defined by the chosen pinched function. -/
theorem range_lineInclusion (s : B (R := K)) :
    Set.range (lineInclusion s) =
      (PrimeSpectrum.basicOpen s.val : Set (PrimeSpectrum K[X])) :=
  PrimeSpectrum.localization_away_comap_range _ s.val

/-- Actual factorization through an affine open, constructed for every endpoint-compatible map. -/
theorem exists_node_factorization
    (f : Spec (.of K[X]) ⟶ X) (hf : f (endpoint 0) = f (endpoint 1)) :
    ∃ (s : B (R := K)), bEval s ≠ 0 ∧
      ∃ (U : X.Opens), IsAffineOpen U ∧
        ∃ k : Spec (.of (OneGonLocalizedPinching.line s)) ⟶ U,
          k ≫ U.ι = lineInclusion s ≫ f := by
  obtain ⟨s, hs, U, hU, hmap⟩ := exists_principal_affine_neighborhood f hf
  have hr : Set.range (lineInclusion s ≫ f) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    apply hmap
    exact (Set.ext_iff.mp (range_lineInclusion s) _).mp ⟨p, rfl⟩
  exact ⟨s, hs, U, hU, IsOpenImmersion.lift U.ι (lineInclusion s ≫ f) hr,
    IsOpenImmersion.lift_fac _ _ _⟩


/-- The section of the affine line defined by a rational endpoint. -/
def endpointSection (a : K) : Spec (.of K) ⟶ Spec (.of K[X]) :=
  Spec.map (CommRingCat.ofHom (evalRingHom a))

open OneGonLocalizedPinching

@[reassoc]
theorem atZero_lineInclusion (s : B (R := K)) (hs : bEval s ≠ 0) :
    Spec.map (CommRingCat.ofHom (atZero s hs)) ≫ lineInclusion s =
      endpointSection 0 := by
  rw [lineInclusion, endpointSection, ← Spec.map_comp]
  congr 1
  apply ConcreteCategory.hom_ext
  intro p
  exact atZero_algebraMap s hs p

@[reassoc]
theorem atOne_lineInclusion (s : B (R := K)) (hs : bEval s ≠ 0) :
    Spec.map (CommRingCat.ofHom (atOne s hs)) ≫ lineInclusion s =
      endpointSection 1 := by
  rw [lineInclusion, endpointSection, ← Spec.map_comp]
  congr 1
  apply ConcreteCategory.hom_ext
  intro p
  exact atOne_algebraMap s hs p

/-- The constructed affine factorization preserves equality of endpoint morphisms,
so it supplies the compatibility required by localized pinching descent. -/
theorem exists_compatible_node_factorization
    (f : Spec (.of K[X]) ⟶ X)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f) :
    ∃ (s : B (R := K)) (hs : bEval s ≠ 0) (U : X.Opens),
      IsAffineOpen U ∧
        ∃ k : Spec (.of (line s)) ⟶ U,
          k ≫ U.ι = lineInclusion s ≫ f ∧
          Spec.map (CommRingCat.ofHom (atZero s hs)) ≫ k =
            Spec.map (CommRingCat.ofHom (atOne s hs)) ≫ k := by
  have hp : f (endpoint 0) = f (endpoint 1) :=
    congrArg (fun g : Spec (.of K) ⟶ X ↦ g ⟨⊥, inferInstance⟩) hf
  obtain ⟨s, hs, U, hU, k, hk⟩ := exists_node_factorization f hp
  refine ⟨s, hs, U, hU, k, hk, ?_⟩
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Category.assoc, hk,
    atZero_lineInclusion_assoc, atOne_lineInclusion_assoc]
  exact hf

end FLT.Mazur.OneGonLocalFactorization
