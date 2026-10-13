/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullInteriorChart
public import FLT.Mazur.AffineHilbertEnvelopeCoaction

/-!
# Source coefficients on full Hilbert envelopes

The original first endpoint defines a morphism from the full independent
translation envelope, even for nonaffine source schemes. Original composition
makes this morphism identical after pullback along the two relation endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
local notation "e" => equivalence f hL d V c k
local notation "m" => composableToProduct f hL d V c k
variable [IsIso (toEnvelope f hL d V c k).left]

/-- The original source endpoint, defined on the whole envelope without an affine hypothesis. -/
def fullEnvelopeSourceMap : (prod A V).left ⟶ A.left := inv (j).left ≫ (p).left

/-- Original composition identifies both endpoint pullbacks of the envelope source map. -/
theorem fullEnvelopeSourceMap_transport :
    (prod.map p (𝟙 V)).left ≫ fullEnvelopeSourceMap f hL d V c k =
      (prod.map q (𝟙 V)).left ≫ fullEnvelopeSourceMap f hL d V c k := by
  let _ := fullEnvelope_composable_isIso f hL d V c k
  apply (cancel_epi (m).left).mp
  have h₁ := congrArg Over.Hom.left (composableToProduct_isPullback f hL d V c k).w
  have h₂ := congrArg Over.Hom.left (composable_fullEnvelope_transport f hL d V c k)
  dsimp only [Over.comp_left] at h₁ h₂
  dsimp only [fullEnvelopeSourceMap]
  rw [← Category.assoc (m).left, ← h₁, Category.assoc,
    IsIso.hom_inv_id_assoc, ← Category.assoc (m).left, ← h₂,
    Category.assoc, IsIso.hom_inv_id_assoc]
  exact (congrArg Over.Hom.left (e).transitivity₁).symm

/-- An actual envelope section pulled from the original first endpoint. -/
def fullEnvelopeSourceSection (s : Γ(A.left, ⊤)) : Γ((prod A V).left, ⊤) :=
  (fullEnvelopeSourceMap f hL d V c k).appTop s

/-- Original composition gives equality of the two transported sections on the entire envelope. -/
theorem fullEnvelopeSourceSection_transport (s : Γ(A.left, ⊤)) :
    (prod.map p (𝟙 V)).left.appTop (fullEnvelopeSourceSection f hL d V c k s) =
      (prod.map q (𝟙 V)).left.appTop (fullEnvelopeSourceSection f hL d V c k s) :=
  congrArg (fun t ↦ t.appTop s) (fullEnvelopeSourceMap_transport f hL d V c k)

/-- The actual full good open carries this envelope section; its affineness is unnecessary. -/
def fullInteriorSourceSection [IsOpenImmersion k.left] [Etale V.hom]
    (s : Γ((fullInteriorSource f hL d V c k).left, ⊤)) :
    Γ((prod (fullInteriorSource f hL d V c k) V).left, ⊤) :=
  fullEnvelopeSourceSection f hL d V c (fullInteriorChart f hL d V c k) s

end FLT.Mazur.HilbertChart.AffineRestriction
