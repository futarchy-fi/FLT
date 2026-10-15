/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAdmissibleKernelOpen
public import FLT.Mazur.AffineHilbertFiniteModelEtaleCertificates

/-!
# Original finite coefficients from admissible generic source coverage

Covering the generic ORIGINAL source fiber by admissible invariant principals
constructs all old generic-kernel inverse neighborhoods. The resulting finite
principal inverses and nonnilpotent coefficient belong to the OLD finite
model. No representative arrows, seed inverse, or global unramifiedness is
assumed. Establishing this source coverage in general remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]

/-- Source coverage constructs nonempty effectivity for the unchanged finite target. -/
theorem finiteModelEffectiveTarget_nonempty_of_admissible_coverage
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ s : compatibleFunctions p q, s ∈ invariantEnvelopeDenominators f hL d V c k ∧
        x ∈ A.left.basicOpen s.val) :
    Nonempty (modelEffectiveTarget f hL d V c k v h).left := by
  apply finiteModelEffectiveTarget_nonempty_of_generic_etale_lifts f hL d V c k
  intro z hz
  obtain ⟨s, hs, hx⟩ := hc (pullback.fst (v).left (v).left z) hz
  let U := SchemeKernelInvariantOpenLift.openDomain (v).left (A.left.basicOpen s.val)
  obtain ⟨a, ha⟩ := admissibleOriginalKernel_exists_lift f hL d V c k s hs
  refine ⟨U.toScheme, U.ι, a, ⟨z, hx⟩, inferInstance, ?_, ?_, rfl⟩
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun t ↦ t ≫ pullback.fst (v).left (v).left) ha
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun t ↦ t ≫ pullback.snd (v).left (v).left) ha

/-- Generic source coverage yields actual original principal inverse and coefficient witnesses. -/
theorem finiteModel_coefficient_of_admissible_coverage
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ s : compatibleFunctions p q, s ∈ invariantEnvelopeDenominators f hL d V c k ∧
        x ∈ A.left.basicOpen s.val) :
    ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ t ∈ s, ∃ a : ((K).basicOpen t).toScheme ⟶ D,
        a ≫ pullback.lift p q h = ((K).basicOpen t).ι) ∧
      (pullback.fst (v).left (v).left ≫ (v).left).appTop r ∈
        Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  (finiteModelEffectiveTarget_nonempty_iff_coefficient f hL d V c k).mp
    (finiteModelEffectiveTarget_nonempty_of_admissible_coverage f hL d V c k hc)

/-- On integral original sources this reaches the represented original Picard fppf region. -/
theorem finiteModelPicardFppfTarget_nonempty_of_admissible_coverage [IsIntegral A.left]
    (hc : ∀ x : A.left, (v).left x = genericPoint T →
      ∃ s : compatibleFunctions p q, s ∈ invariantEnvelopeDenominators f hL d V c k ∧
        x ∈ A.left.basicOpen s.val) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  (finiteModelPicardFppfTarget_nonempty_iff_coefficient f hL d V c k).mpr
    (finiteModel_coefficient_of_admissible_coverage f hL d V c k hc)

end FLT.Mazur.HilbertChart.AffineRestriction
