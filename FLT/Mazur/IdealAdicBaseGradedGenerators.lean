/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicBasePowerGenerators
public import FLT.Mazur.IdealAdicGradedBaseAlgebra

/-!
# Base generators of the actual graded quotients

Quotienting the affine power spanning theorem gives spanning by the actual
base graded comparison. The same comparison extends to a ring homomorphism
on every source open, retaining its homogeneous components.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open FLT.Mazur.IdealAdicGradedSections
open FLT.Mazur.CoherentIdealIntersection

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Restrict the actual graded comparison from the affine base to a source open. -/
def gradedSection (n : ℕ) (U : X.Opens) (s : Piece J ⊤ n) : Piece (J.comap f) U n :=
  (idealGraded (J.comap f) n).presheaf.map (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op
    (pull J f n ⊤ s)

/-- The local graded generator is the quotient of the original power generator. -/
lemma gradedSection_projection (n : ℕ) (U : X.Opens)
    (s : Γ(idealModule (J ^ n), ⊤)) :
    gradedSection J f n U ((cokernel.π (idealStep J n)).app ⊤ s) =
      (cokernel.π (idealStep (J.comap f) n)).app U (powerSection J f n U s) := by
  unfold gradedSection
  rw [pull_projection]
  exact (PresheafOfModules.naturality_apply (cokernel.π (idealStep (J.comap f) n)).val
    (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤)).op ((powerMap J f n).app ⊤ s)).symm

variable [IsLocallyNoetherian X] [IsAffine Y]

/-- Base graded sections span the actual graded coefficient on each affine source open. -/
lemma gradedSection_span (n : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U.1) (Set.range (gradedSection J f n U.1)) = ⊤ := by
  let q : Γ(idealModule (J.comap f ^ n), U.1) →ₗ[Γ(X, U.1)]
      Piece (J.comap f) U.1 n :=
    ((cokernel.π (idealStep (J.comap f) n)).val.app (op U.1)).hom
  have := idealModule_coherent (J.comap f ^ n)
  have : (cokernel (idealStep (J.comap f) n)).IsFinitePresentation :=
    idealGraded_coherent (J.comap f) n
  have hq : Function.Surjective q := GlobalIdealPower.affine_epi_surjective _ U
  have h : (Submodule.span Γ(X, U.1) (Set.range (powerSection J f n U.1))).map q ≤
      Submodule.span Γ(X, U.1) (Set.range (gradedSection J f n U.1)) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨(cokernel.π (idealStep J n)).app ⊤ s, gradedSection_projection J f n U.1 s⟩
  rw [powerSection_span, Submodule.map_top, LinearMap.range_eq_top.mpr hq] at h
  exact top_unique h

variable [IsLocallyNoetherian Y]

/-- The actual graded base algebra maps canonically to every source open. -/
def localRingHom (U : X.Opens) :
    IdealAdicGradedSections.Sections J ⊤ →+* IdealAdicGradedSections.Sections (J.comap f) U :=
  (restrictRingHom (J.comap f) U (homOfLE (by simp : U ≤ f ⁻¹ᵁ ⊤))).comp
    (ringHom J f ⟨⊤, isAffineOpen_top Y⟩)

/-- The local total comparison retains the graded quotient comparison. -/
lemma localRingHom_of (U : X.Opens) (n : ℕ) (s : Piece J ⊤ n) :
    localRingHom J f U (of J ⊤ n s) = of (J.comap f) U n (gradedSection J f n U s) := by
  change restrict (J.comap f) U _ (sumMap J f ⟨⊤, isAffineOpen_top Y⟩ (of J ⊤ n s)) = _
  rw [sumMap_of, restrict_of]
  rfl

/-- The base graded algebra acts on the total coefficient over each source open. -/
@[instance_reducible]
def localBaseAlgebra (U : X.Opens) :
    Algebra (IdealAdicGradedSections.Sections J ⊤)
      (IdealAdicGradedSections.Sections (J.comap f) U) :=
  (localRingHom J f U).toAlgebra

end FLT.Mazur.IdealAdicGradedPullback
