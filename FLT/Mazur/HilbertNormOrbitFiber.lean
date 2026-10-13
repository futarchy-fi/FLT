/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertInvariantRegularNorm
public import FLT.Mazur.SchemeTranslationNormFiber

/-!
# Nonvanishing of Hilbert norms on entire original orbits

The constructed source section and envelope isomorphism identify the full
fiber norm criterion with all first endpoints over the original second endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
/-- The original translation structural algebra for orbit norms. -/
local instance orbitNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
variable [IsIso (toEnvelope f hL d V c k).left]

omit [IsAffine V.left] in
/-- Pulling the constructed envelope section back recovers the original first endpoint. -/
theorem fullEnvelopeSourceSection_pullback (s : Γ(A.left, ⊤)) :
    (j).left.appTop (fullEnvelopeSourceSection f hL d V c k s) = (p).left.appTop s := by
  change ((j).left ≫ inv (j).left ≫ (p).left).appTop s = _
  rw [IsIso.hom_inv_id_assoc]

/-- The full regular norm detects every original orbit endpoint, without an affine source. -/
theorem mem_basicOpen_fullEnvelopeNorm_iff (s : Γ(A.left, ⊤)) (x : A.left) :
    x ∈ A.left.basicOpen (fullEnvelopeRegularNorm f hL d V c k b s) ↔
      ∀ z : (relation f hL d V c k).left, (q).left z = x →
        (p).left z ∈ A.left.basicOpen s := by
  rw [fullEnvelopeRegularNorm, mem_basicOpen_regularNorm_iff]
  have hj (z : (relation f hL d V c k).left) :
      (j).left z ∈ (prod A V).left.basicOpen (fullEnvelopeSourceSection f hL d V c k s) ↔
        (p).left z ∈ A.left.basicOpen s := by
    change z ∈ (j).left ⁻¹ᵁ (prod A V).left.basicOpen
      (fullEnvelopeSourceSection f hL d V c k s) ↔ z ∈ (p).left ⁻¹ᵁ A.left.basicOpen s
    rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top,
      fullEnvelopeSourceSection_pullback]
  have hq (z : (relation f hL d V c k).left) :
      (prod.fst : prod A V ⟶ A).left ((j).left z) = (q).left z :=
    congrArg (fun g : relation f hL d V c k ⟶ A ↦ g.left z)
      (toEnvelope_test f hL d V c k)
  constructor
  · intro h z hz
    exact (hj z).mp (h _ ((hq z).trans hz))
  · intro h y hy
    obtain ⟨z, rfl⟩ := (j).left.homeomorph.surjective y
    exact (hj z).mpr (h z ((hq z).symm.trans hy))

end FLT.Mazur.HilbertChart.AffineRestriction
