/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingEqualizerLocalDescent
public import FLT.Mazur.RelativePinchingNeighborhoods
/-!
# Local descent at every relative pinching point

The saturated neighborhoods and localized equalizer give genuine morphisms
near each node over every base prime, for arbitrary commutative rings.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
universe u
namespace FLT.Mazur.RelativePinchingLocalDescent
open PolygonNodePresentation PolygonNodeEqualizer RelativePinchingNeighborhoods
open RingEqualizerLocalDescent RingEqualizerLocalization
variable {R : Type u} [CommRing R]
/-- View a one-gon function in the ring equalizer. -/
def oneGonDenominator (s : B (R := R)) :
    (evalRingHom (0 : R)).eqLocus (evalRingHom 1) := ⟨s.val, s.property⟩

/-- Local one-gon descent near a specified prime of the base. -/
theorem oneGon_exists_local_desc {Y : Scheme.{u}} (h : Spec (.of R[X]) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ h =
      Spec.map (CommRingCat.ofHom (evalRingHom (1 : R))) ≫ h) (x : PrimeSpectrum R) :
    ∃ (s : B (R := R))
      (d : Spec (.of (E (evalRingHom (0 : R)) (evalRingHom (1 : R))
        (oneGonDenominator s))) ⟶ Y),
      bEval s ∉ x.asIdeal ∧
        branch (evalRingHom (0 : R)) (evalRingHom (1 : R)) (oneGonDenominator s) ≫ d =
          branchOpen (evalRingHom (0 : R)) (evalRingHom (1 : R)) (oneGonDenominator s) ≫ h := by
  have ho : h (point 0 x) = h (point 1 x) := congrArg (fun k ↦ k x) w
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := h (point 0 x)) (by trivial)
  obtain ⟨s, hs, hV⟩ := oneGon_neighborhood x (h ⁻¹ᵁ U) hoU
    (by change h (point 1 x) ∈ U; rwa [← ho])
  obtain ⟨d, hd⟩ := desc_on_open (evalRingHom (0 : R)) (evalRingHom (1 : R))
    (oneGonDenominator s) h w U hU hV
  exact ⟨s, d, hs, hd⟩

/-- Evaluate the first normalization branch at zero. -/
def nodeFirst : R[X] × R[X] →+* R := (evalRingHom 0).comp (RingHom.fst _ _)
/-- Evaluate the second normalization branch at zero. -/
def nodeSecond : R[X] × R[X] →+* R := (evalRingHom 0).comp (RingHom.snd _ _)
/-- View a node function in the ring equalizer. -/
def nodeDenominator (s : A (R := R)) :
    (nodeFirst (R := R)).eqLocus nodeSecond := ⟨s.val, s.property⟩

/-- A principal open of a product is controlled by its two branches. -/
theorem prod_basicOpen_le {C D : Type*} [CommRing C] [CommRing D]
    (p : C) (q : D) (U : Opens (PrimeSpectrum (C × D)))
    (h₁ : ∀ z : PrimeSpectrum C, z ∈ PrimeSpectrum.basicOpen p →
      PrimeSpectrum.comap (RingHom.fst C D) z ∈ U)
    (h₂ : ∀ z : PrimeSpectrum D, z ∈ PrimeSpectrum.basicOpen q →
      PrimeSpectrum.comap (RingHom.snd C D) z ∈ U) :
    PrimeSpectrum.basicOpen (p, q) ≤ U := by
  intro z hz
  obtain ⟨t, rfl⟩ := (PrimeSpectrum.primeSpectrumProd C D).symm.surjective z
  cases t with
  | inl z =>
    rw [PrimeSpectrum.primeSpectrumProd_symm_inl] at hz ⊢
    exact h₁ z hz
  | inr z =>
    rw [PrimeSpectrum.primeSpectrumProd_symm_inr] at hz ⊢
    exact h₂ z hz

/-- Local node descent near a specified prime of the base. -/
theorem node_exists_local_desc {Y : Scheme.{u}} (h : Spec (.of (R[X] × R[X])) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (nodeFirst (R := R))) ≫ h =
      Spec.map (CommRingCat.ofHom nodeSecond) ≫ h) (x : PrimeSpectrum R) :
    ∃ (s : A (R := R)) (d : Spec (.of (E nodeFirst nodeSecond (nodeDenominator s))) ⟶ Y),
      aEval s ∉ x.asIdeal ∧
        branch nodeFirst nodeSecond (nodeDenominator s) ≫ d =
          branchOpen nodeFirst nodeSecond (nodeDenominator s) ≫ h := by
  let h₁ := Spec.map (CommRingCat.ofHom (RingHom.fst R[X] R[X])) ≫ h
  let h₂ := Spec.map (CommRingCat.ofHom (RingHom.snd R[X] R[X])) ≫ h
  have ho : h₁ (point 0 x) = h₂ (point 0 x) := congrArg (fun k ↦ k x) w
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := h₁ (point 0 x)) (by trivial)
  obtain ⟨s, hs, hV, hW⟩ := node_neighborhood x (h₁ ⁻¹ᵁ U) (h₂ ⁻¹ᵁ U) hoU
    (by change h₂ (point 0 x) ∈ U; rwa [← ho])
  have hsU : PrimeSpectrum.basicOpen s.val ≤ h ⁻¹ᵁ U :=
    prod_basicOpen_le (first s) (second s) (h ⁻¹ᵁ U) (fun _ hz ↦ hV hz) (fun _ hz ↦ hW hz)
  obtain ⟨d, hd⟩ := desc_on_open nodeFirst nodeSecond (nodeDenominator s) h w U hU hsU
  exact ⟨s, d, hs, hd⟩
end FLT.Mazur.RelativePinchingLocalDescent
