/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteEnvelopeSeed
public import FLT.Mazur.AffineHilbertFiniteModelPrincipalInverses

/-!
# Effective finite-model neighborhoods constructed from full envelopes

The explicit inverse fills the whole kernel inverse locus and the whole
unchanged effective target. Nonempty sources therefore give nonnilpotent
coefficient certificates. For integral sources the existing generic-flatness
construction also gives a nonempty represented original Picard fppf target.
Full target effectivity alone does not assert full target image or flatness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [IsIso (toEnvelope f hL d V c k).left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "m" => pullback.lift p q h
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "T" => Over.left (finiteKernelModel f hL d V c k)
local notation "D" => Over.left (relation f hL d V c k)
local notation "b" => pullback.fst (Over.Hom.left v) (Over.Hom.left v) ≫ (Over.Hom.left v)

/-- The constructed global inverse supplies the entire original kernel inverse locus. -/
theorem finiteEnvelope_inverseLocus_top : MonomorphismOpenImage.locus m = ⊤ := by
  apply top_le_iff.mp
  exact MonomorphismOpenImage.le_locus m ⊤
    ((⊤ : (K).Opens).ι ≫ finiteEnvelopeKernelInverse f hL d V c k)
    (by rw [Category.assoc, finiteEnvelopeKernelInverse_comp, Category.comp_id])

/-- The unchanged effective target is full, including points with empty source fiber. -/
theorem finiteEnvelope_effectiveTargetOpen_top : KernelPairEffectiveOpen.targetOpen p q
    (v).left h = ⊤ := by
  change SchemeWholeFiberOpen.locus b (MonomorphismOpenImage.locus m) = ⊤
  rw [finiteEnvelope_inverseLocus_top, SchemeWholeFiberOpen.locus_top]

/-- Every actual original source point constructs a point of the effective finite target. -/
theorem finiteEnvelope_effectiveTarget_nonempty [Nonempty A.left] :
    Nonempty (modelEffectiveTarget f hL d V c k v h).left := by
  obtain ⟨x⟩ := ‹Nonempty A.left›
  refine ⟨⟨(v).left x, ?_⟩⟩
  change (v).left x ∈ KernelPairEffectiveOpen.targetOpen p q (v).left h
  rw [finiteEnvelope_effectiveTargetOpen_top]
  trivial

/-- Actual principal inverses and a nonnilpotent original coefficient now require no seed input. -/
theorem finiteEnvelope_coefficient [Nonempty A.left] :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D, a ≫ m = ((K).basicOpen t).ι) ∧
      (b).appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  (finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k).mp
    (finiteEnvelope_effectiveTarget_nonempty f hL d V c k)

/-- On integral original sources the constructed finite model has a represented fppf region. -/
theorem finiteEnvelope_picardFppfTarget_nonempty [IsIntegral A.left] :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  (finiteModelPicardFppfTarget_nonempty_iff_coefficient f hL d V c k).mpr
    (finiteEnvelope_coefficient f hL d V c k)

end FLT.Mazur.HilbertChart.AffineRestriction
