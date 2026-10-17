/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryKernelLinearOperator
public import FLT.Mazur.FiniteKernelCorrectionLocalizedKernel

/-!
# Localizing the actual geometric finite kernel operator

All scalar actions are the original invariant actions. The localized finite
operator still sees the whole localized boundary kernel and clears every
solution to an original scalar multiplier and ambient coefficient tuple.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency true
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

attribute [local instance] originalAmbientSourceAlgebra originalAmbientRelationAlgebra
  originalAmbientBoundaryAlgebra
local notation "p₁" => originalAmbientFirstAlgHom f hL d V c k W
local notation "q₁" => originalAmbientSecondAlgHom f hL d V c k W
local notation "r₁" => originalAmbientBoundaryAlgHom f hL d V c k W
local notation "F" => originalAmbientCorrectionLinearMap f hL d V c k W hW
attribute [local irreducible] originalAmbientFirstAlgHom originalAmbientSecondAlgHom
  originalAmbientBoundaryAlgHom originalAmbientCorrectionLinearMap
  invariantSheaf sourceSheaf relationSheaf
  FiniteKernelCorrections.localizedMap

variable (U : Submonoid
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

/-- The actual finite correction operator localized only in original invariant scalars. -/
def originalAmbientLocalizedCorrection :
    LocalizedModule U (Fin n → Q) →ₗ[Ω] LocalizedModule U C₀ :=
  FiniteKernelCorrections.localizedMap U F

/-- The actual localized operator has the full localized boundary-kernel image. -/
theorem originalAmbientLocalizedCorrection_range :
    LinearMap.range (originalAmbientLocalizedCorrection f hL d V c k W hW U) =
      Submodule.map (FiniteKernelCorrections.localizedMap U
        ((p₁).toLinearMap - (q₁).toLinearMap))
        (LinearMap.ker (FiniteKernelCorrections.localizedMap U (r₁).toLinearMap)) := by
  unfold originalAmbientLocalizedCorrection originalAmbientCorrectionLinearMap
  apply FiniteKernelCorrections.localized_operator_range U v r₁
  unfold originalAmbientBoundaryAlgHom
  exact originalAmbientBoundaryFrame_span f hL d V c k W hW

/-- Every localized correction gives an exact original finite-coordinate equation. -/
theorem originalAmbientLocalizedCorrection_iff (x : C₀) :
    (∃ w : LocalizedModule U (Fin n → Q), LocalizedModule.mk x (1 : U) +
      originalAmbientLocalizedCorrection f hL d V c k W hW U w = 0) ↔
      ∃ a : U, ∃ u : Fin n → Q,
        p₀ (ι₀ a.val) * x +
          ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0 := by
  unfold originalAmbientLocalizedCorrection
  rw [FiniteKernelCorrections.localized_correction_iff]
  apply exists_congr
  intro a
  apply exists_congr
  intro u
  rw [originalAmbientCorrectionLinearMap_apply]
  rfl

end FLT.Mazur.HilbertChart.AffineRestriction
