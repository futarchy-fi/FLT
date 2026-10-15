/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAdmissibleOldKernel
public import FLT.Mazur.AffineHilbertFiniteInvariantOpens
public import FLT.Mazur.SchemeKernelInvariantOpenLift

/-!
# Admissible coefficients construct open inverses in the original global kernel

Each actual admissible original coefficient supplies an inverse on the OLD
finite kernel wherever its first endpoint lies in the coefficient's principal
source. Saturation proves that the second endpoint survives too. This is a
certificate inside the original finite model, not only a fresh local model.
Arbitrary coverage by such coefficients remains a separate geometric task.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
  (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "U" => SchemeKernelInvariantOpenLift.openDomain v (A.left.basicOpen s.val)
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s

include hs in
/-- Construct an actual original relation arrow on an OPEN of the unchanged finite kernel. -/
theorem admissibleOriginalKernel_exists_lift :
    ∃ a : (U).toScheme ⟶ (relation f hL d V c k).left,
      a ≫ pullback.lift p q h = (U).ι := by
  have H := admissibleOldFinite_isPullback f hL d V c k s hs
  unfold invariantPrincipalChart at H
  exact SchemeKernelInvariantOpenLift.exists_lift p q v h (A.left.basicOpen s.val)
    (finiteKernel_invariant_preimage f hL d V c k s)
    (fst f hL d V c (u ≫ k)).left (snd f hL d V c (u ≫ k)).left
    (nestedToFullRelation f hL d V c k u).left
    (congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u))
    (congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u)) H

include hs in
/-- Admissible principal neighborhoods fill the corresponding old kernel inverse open. -/
theorem admissibleOriginalKernel_le_inverseLocus :
    U ≤ MonomorphismOpenImage.locus (pullback.lift p q h) := by
  obtain ⟨a, ha⟩ := admissibleOriginalKernel_exists_lift f hL d V c k s hs
  exact MonomorphismOpenImage.le_locus _ U a ha

include hs in
/-- Every original kernel branch above this principal source has an actual original preimage. -/
theorem admissibleOriginalKernel_image (z : (pullback v v : Scheme))
    (hz : pullback.fst v v z ∈ A.left.basicOpen s.val) :
    z ∈ Set.range (pullback.lift p q h) := by
  obtain ⟨a, ha⟩ := admissibleOriginalKernel_exists_lift f hL d V c k s hs
  exact ⟨a ⟨z, hz⟩, congrArg (fun t ↦ t ⟨z, hz⟩) ha⟩

end FLT.Mazur.HilbertChart.AffineRestriction
