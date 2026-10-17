/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryAmbientFrame
public import FLT.Mazur.FiniteKernelCorrectionOperator

/-!
# The actual finite-coordinate boundary correction operator

Original invariant scalars act on the ambient source, boundary source and full
relation. Both endpoints are linear over these scalars. The constructed finite
ideal frame gives an operator whose image is the full boundary kernel's
relation-difference image, not merely a submodule of convenient corrections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Q" => (sourceSheaf e).obj.obj (op W)
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)

local notation "D₀" => (invariantSheaf ec).obj.obj (op Wc)
local notation "r₀" => originalAmbientBoundaryRestriction f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryRestriction
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

local notation "v" => originalAmbientBoundaryFrame f hL d V c k W hW
local notation "n" => originalAmbientBoundaryFrameSize f hL d V c k W hW
local notation "p₀" => ((firstRestriction e).hom.app (op W)).hom
local notation "q₀" => ((secondRestriction e).hom.app (op W)).hom
local notation "ρ" => originalClosedSectionPullback f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryFrame originalAmbientBoundaryFrameSize
  originalAmbientBoundaryLift

local notation "ι₀" => ((invariantInclusion e).hom.app (op W)).hom
local notation "ιc" => ((invariantInclusion ec).hom.app (op Wc)).hom

local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "C₀" => (relationSheaf e).obj.obj (op W)

/-- Original invariant scalars act on the unchanged ambient source. -/
@[instance_reducible]
def originalAmbientSourceAlgebra : Algebra Ω Q := (ι₀).toAlgebra

/-- The full relation receives its scalar action from either invariant endpoint. -/
@[instance_reducible]
def originalAmbientRelationAlgebra : Algebra Ω C₀ := ((p₀).comp ι₀).toAlgebra

/-- Boundary source scalars use the original invariant restriction. -/
@[instance_reducible]
def originalAmbientBoundaryAlgebra : Algebra Ω T := ((ιc).comp ρ).toAlgebra

attribute [local instance] originalAmbientSourceAlgebra originalAmbientRelationAlgebra
  originalAmbientBoundaryAlgebra

/-- The first full endpoint as a map over original invariant scalars. -/
def originalAmbientFirstAlgHom : Q →ₐ[Ω] C₀ where
  __ := p₀
  commutes' _ := rfl

/-- The independent second endpoint has the same original invariant scalars. -/
def originalAmbientSecondAlgHom : Q →ₐ[Ω] C₀ where
  __ := q₀
  commutes' a := (invariantSection_condition e W a).symm

/-- Actual closed-source restriction respects the original invariant scalar action. -/
def originalAmbientBoundaryAlgHom : Q →ₐ[Ω] T where
  __ := r₀
  commutes' a := originalAmbientBoundaryRestriction_invariant f hL d V c k W a

local notation "p₁" => originalAmbientFirstAlgHom f hL d V c k W
local notation "q₁" => originalAmbientSecondAlgHom f hL d V c k W
local notation "r₁" => originalAmbientBoundaryAlgHom f hL d V c k W
attribute [local irreducible] originalAmbientFirstAlgHom originalAmbientSecondAlgHom
  originalAmbientBoundaryAlgHom

/-- All ambient kernel corrections in finitely many original source coordinates. -/
def originalAmbientCorrectionLinearMap : (Fin n → Q) →ₗ[Ω] C₀ :=
  FiniteKernelCorrections.operator Ω v p₁ q₁

/-- Evaluation of the actual operator retains both endpoint actions on each coefficient. -/
theorem originalAmbientCorrectionLinearMap_apply (u : Fin n → Q) :
    originalAmbientCorrectionLinearMap f hL d V c k W hW u =
      ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) := by
  unfold originalAmbientCorrectionLinearMap
  rw [FiniteKernelCorrections.operator_apply]
  unfold originalAmbientFirstAlgHom originalAmbientSecondAlgHom
  rfl

/-- The finite-coordinate image is exactly the full original kernel correction image. -/
theorem originalAmbientCorrectionLinearMap_range :
    LinearMap.range (originalAmbientCorrectionLinearMap f hL d V c k W hW) =
      Submodule.map ((p₁).toLinearMap - (q₁).toLinearMap) (LinearMap.ker (r₁).toLinearMap) := by
  unfold originalAmbientCorrectionLinearMap
  apply FiniteKernelCorrections.operator_range
  unfold originalAmbientBoundaryAlgHom
  exact originalAmbientBoundaryFrame_span f hL d V c k W hW

end FLT.Mazur.HilbertChart.AffineRestriction
