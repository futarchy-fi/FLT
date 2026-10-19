/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryPrincipalTestCharts
public import FLT.Mazur.AffineValuationGeneratorLift
public import FLT.Mazur.SchemeValuationImageClosure

/-!
# Exact scalar-center valuation witnesses on finitely many full test charts

The finite original test family supplies a finite affine atlas for the failure
of its equations. Every excluded scalar prime gives an exact-center square on
one of these full charts. Matching exact fibers force nonextension there.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "chart" => boundaryTestChart s κ
local notation "φ" t => scalarMorphism (boundaryTestChartScalar s κ t)

/-- An excluded scalar prime has a finite-test chart square at an original minimal component. -/
theorem boundaryTestChart_component_square (P : PrimeSpectrum T)
    (hP : P ∉ boundaryScalarNilpotenceOpen s κ a) :
    ∃ (t : a) (Q : minimalPrimes C) (S : ValuativeCommSq (φ t.val)),
      (chart t.val).ι (S.i₁ default) = boundaryComponentPoint s κ Q ∧
      S.i₂ (closedPoint S.R) = P := by
  have h := (mem_boundaryScalarNilpotenceOpen_iff_components s κ a P).not.mp hP
  push Not at h
  obtain ⟨Q, hc, hQ⟩ := h
  have hn : ¬ ∀ t ∈ a, t ∈ (boundaryProjection s κ (boundaryComponentPoint s κ Q)).asIdeal := by
    intro h
    apply hQ
    rw [boundaryTestIdeal, Ideal.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((boundaryComponent_equation_iff s κ Q t).mpr (h t ht))
  push Not at hn
  obtain ⟨t, ht, hn⟩ := hn
  have hm := (mem_boundaryTestChart s κ t (boundaryComponentPoint s κ Q)).mpr hn
  let x : (chart t).toScheme := ⟨boundaryComponentPoint s κ Q, hm⟩
  have hx : (φ t) x ⤳ P := by
    rw [boundaryTestChartScalar_morphism]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hc
  obtain ⟨S, hS, hcenter⟩ := SchemeSpecializationValuation.exists_square (φ t) x P hx
  exact ⟨⟨t, ht⟩, Q, S, congrArg (fun y ↦ (chart t).ι y) hS, hcenter⟩

/-- Every exact-center square on a selected test chart certifies original scalar exclusion. -/
theorem boundaryTestChart_square_excludes (P : PrimeSpectrum T) (t : a)
    (S : ValuativeCommSq (φ t.val)) (hS : S.i₂ (closedPoint S.R) = P) :
    P ∉ boundaryScalarNilpotenceOpen s κ a := by
  have hs := SchemeSpecializationValuation.square_specializes (φ t.val) S
  rw [hS] at hs
  intro hp
  have hg := hs.mem_open (boundaryScalarNilpotenceOpen s κ a).isOpen hp
  rw [congrArg (fun f ↦ f (S.i₁ default))
    (boundaryTestChartScalar_morphism s κ t.val)] at hg
  have hm := boundaryScalarNilpotenceOpen_preimage s κ a hg
  rw [boundaryNilpotenceOpen_eq_interior s κ a 0] at hm
  have hz := interior_subset hm
  rw [mem_boundaryTestThickening_range] at hz
  exact (mem_boundaryTestChart s κ t.val _).mp (S.i₁ default).property (hz t.val t.property)

/-- The finite affine test atlas detects precisely the full original scalar obstruction. -/
theorem boundaryTestChart_square_iff (P : PrimeSpectrum T) :
    (∃ (t : a) (S : ValuativeCommSq (φ t.val)), S.i₂ (closedPoint S.R) = P) ↔
      P ∉ boundaryScalarNilpotenceOpen s κ a := by
  constructor
  · rintro ⟨t, S, hS⟩
    exact boundaryTestChart_square_excludes s κ a P t S hS
  · intro hP
    obtain ⟨t, _, S, _, hc⟩ := boundaryTestChart_component_square s κ a P hP
    exact ⟨t, S, hc⟩

/-- Matching exact fibers force nonextension on the full affine principal test charts. -/
theorem boundaryTestChart_no_lift (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal)
    (t : a) (S : ValuativeCommSq (φ t.val)) (hS : S.i₂ (closedPoint S.R) = P) :
    ¬ S.commSq.HasLift := by
  intro hl
  obtain ⟨l⟩ := (CommSq.HasLift.iff S.commSq).mp hl
  have hc := (SchemeSpecializationValuation.lift_specializes (φ t.val) S l).2.trans hS
  rw [congrArg (fun f ↦ f (l.l (closedPoint S.R)))
    (boundaryTestChartScalar_morphism s κ t.val)] at hc
  exact (mem_boundaryTestChart s κ t.val _).mp
    (l.l (closedPoint S.R)).property (hf _ hc t.val t.property)

/-- Matching fibers and extensions on finitely many full charts exclude all residual components. -/
theorem boundaryScalar_mem_of_testChart_lifts (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal)
    (hl : ∀ (t : a) (S : ValuativeCommSq (φ t.val)),
      S.i₂ (closedPoint S.R) = P → S.commSq.HasLift) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  by_contra hp
  obtain ⟨t, S, hS⟩ := (boundaryTestChart_square_iff s κ a P).mpr hp
  exact boundaryTestChart_no_lift s κ a P hf t S hS (hl t S hS)

end FLT.Mazur.AffineScalarBoundaryNilpotence
