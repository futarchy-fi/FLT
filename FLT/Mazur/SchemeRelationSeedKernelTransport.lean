/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOrbitAtlasKernel

/-!
# Transporting partial seed kernel certificates

Pull back the original seed comparison along the two independent seed
coordinates of the orbit kernel. Original arrow transport gives a morphism
from this pullback into the original relation. Thus seed kernel image
certificates propagate even when the seed kernel is not globally effective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedKernelTransport
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "π" => pullback.snd q.left a
local notation "r" => pullback.fst q.left a
local notation "K" => (pullback (b ≫ w) (b ≫ w) : Scheme)
local notation "x" => pullback.fst (b ≫ w) (b ≫ w)
local notation "y" => pullback.snd (b ≫ w) (b ≫ w)

include h in
/-- The original coefficient equation restricts to the full seed relation. -/
theorem seed_condition : fst p.left q.left a ≫ (a ≫ w) =
    snd p.left q.left a ≫ (a ≫ w) := by
  rw [← Category.assoc, ← Category.assoc, ← arrow_fst, ← arrow_snd]
  rw [Category.assoc, Category.assoc, h]

/-- The seed comparison retains both seed coordinates and the original arrow. -/
def seedComparison : doubleDomain p.left q.left a ⟶ pullback (a ≫ w) (a ≫ w) :=
  pullback.lift (fst p.left q.left a) (snd p.left q.left a) (seed_condition w h a)

@[reassoc]
theorem seedComparison_fst : seedComparison w h a ≫ pullback.fst (a ≫ w) (a ≫ w) =
    fst p.left q.left a := pullback.lift_fst ..

@[reassoc]
theorem seedComparison_snd : seedComparison w h a ≫ pullback.snd (a ≫ w) (a ≫ w) =
    snd p.left q.left a := pullback.lift_snd ..

/-- Both independent coordinates of the propagated kernel map to the seed kernel. -/
def toSeedKernel : K ⟶ pullback (a ≫ w) (a ≫ w) :=
  pullback.lift (x ≫ π) (y ≫ π) (by
    simpa only [Category.assoc,
      ← SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a] using
      pullback.condition (f := b ≫ w) (g := b ≫ w))

@[reassoc]
theorem toSeedKernel_fst : toSeedKernel w h a ≫ pullback.fst (a ≫ w) (a ≫ w) = x ≫ π :=
  pullback.lift_fst ..

@[reassoc]
theorem toSeedKernel_snd : toSeedKernel w h a ≫ pullback.snd (a ≫ w) (a ≫ w) = y ≫ π :=
  pullback.lift_snd ..

local notation "m" => seedComparison w h a
local notation "t" => toSeedKernel w h a
local notation "u" => pullback.fst m t
local notation "v" => pullback.snd m t

/-- The certificate pullback has exactly the first endpoint required for original transport. -/
theorem certificate_fst : (u ≫ arrow p.left q.left a) ≫ p.left = (v ≫ x ≫ r) ≫ q.left := by
  have H := congrArg (fun f ↦ f ≫ pullback.fst (a ≫ w) (a ≫ w))
    (pullback.condition (f := m) (g := t))
  simp only [Category.assoc, seedComparison_fst, toSeedKernel_fst] at H
  rw [Category.assoc, arrow_fst, ← Category.assoc, H]
  simp only [Category.assoc, pullback.condition]

/-- The second endpoint is retained independently in the certificate pullback. -/
theorem certificate_snd : (u ≫ arrow p.left q.left a) ≫ q.left = (v ≫ y ≫ r) ≫ q.left := by
  have H := congrArg (fun f ↦ f ≫ pullback.snd (a ≫ w) (a ≫ w))
    (pullback.condition (f := m) (g := t))
  simp only [Category.assoc, seedComparison_snd, toSeedKernel_snd] at H
  rw [Category.assoc, arrow_snd, ← Category.assoc, H]
  simp only [Category.assoc, pullback.condition]

/-- Partial seed certificates construct literal original arrows on their pullback. -/
def certificateArrow : pullback m t ⟶ D.left :=
  untransportOriginal e (v ≫ x ≫ r) (v ≫ y ≫ r) (u ≫ arrow p.left q.left a)
    (certificate_fst w h a) (certificate_snd w h a)

@[reassoc]
theorem certificateArrow_fst : certificateArrow e w h a ≫ p.left = v ≫ x ≫ b := by
  rw [certificateArrow, untransportOriginal_fst]
  simp only [SchemeRelationEtaleBranchPropagation.branch, Category.assoc]

@[reassoc]
theorem certificateArrow_snd : certificateArrow e w h a ≫ q.left = v ≫ y ≫ b := by
  rw [certificateArrow, untransportOriginal_snd]
  simp only [SchemeRelationEtaleBranchPropagation.branch, Category.assoc]

/-- The canonical map from the propagated coefficient kernel to the original one. -/
def toOriginalKernel : K ⟶ pullback w w :=
  pullback.map (b ≫ w) (b ≫ w) w w b b (𝟙 T)
    (Category.comp_id _) (Category.comp_id _)

@[reassoc]
theorem toOriginalKernel_fst : toOriginalKernel w a ≫ pullback.fst w w = x ≫ b :=
  pullback.lift_fst ..

@[reassoc]
theorem toOriginalKernel_snd : toOriginalKernel w a ≫ pullback.snd w w = y ≫ b :=
  pullback.lift_snd ..

/-- Transport respects the original coefficient kernel as a scheme morphism. -/
@[reassoc]
theorem certificateArrow_comparison : certificateArrow e w h a ≫
    pullback.lift p.left q.left h = v ≫ toOriginalKernel w a := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, certificateArrow_fst,
      Category.assoc, toOriginalKernel_fst]
  · rw [Category.assoc, pullback.lift_snd, certificateArrow_snd,
      Category.assoc, toOriginalKernel_snd]

include e in
/-- A seed image certificate covers every residue-field branch of the original kernel map. -/
theorem mem_image (z : K) (hz : toSeedKernel w h a z ∈ Set.range (seedComparison w h a)) :
    toOriginalKernel w a z ∈ Set.range (pullback.lift p.left q.left h) := by
  obtain ⟨d, hd⟩ := hz
  obtain ⟨c, _, hc⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback m t) d z hd
  refine ⟨certificateArrow e w h a c, ?_⟩
  exact (congrArg (fun f ↦ f c) (certificateArrow_comparison e w h a)).trans
    (congrArg (toOriginalKernel w a) hc)

end FLT.Mazur.SchemeRelationSeedKernelTransport
