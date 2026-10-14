/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedKernelTransport

/-!
# The full seed comparison is the original comparison pulled back

Both seed coordinates, including their common coefficient coordinate, remain
in the cartesian square. Seed image certificates are therefore detected by
the original kernel image, with no flatness or monicity of the seed map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedKernelTransport
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "C" => (pullback (a ≫ w) (a ≫ w) : Scheme)
local notation "m" => pullback.lift p.left q.left h
local notation "s" => seedComparison w h a

/-- The actual map of seed and original coefficient kernels. -/
def seedToOriginalKernel : C ⟶ pullback w w :=
  pullback.map (a ≫ w) (a ≫ w) w w a a (𝟙 T)
    (Category.comp_id _) (Category.comp_id _)

@[reassoc]
theorem seedToOriginalKernel_fst : seedToOriginalKernel w a ≫ pullback.fst w w =
    pullback.fst (a ≫ w) (a ≫ w) ≫ a := pullback.lift_fst ..

@[reassoc]
theorem seedToOriginalKernel_snd : seedToOriginalKernel w a ≫ pullback.snd w w =
    pullback.snd (a ≫ w) (a ≫ w) ≫ a := pullback.lift_snd ..

/-- The full restriction retains the literal original comparison. -/
theorem seedComparison_square : arrow p.left q.left a ≫ m = s ≫ seedToOriginalKernel w a := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, arrow_fst,
      Category.assoc, seedToOriginalKernel_fst, seedComparison_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, arrow_snd,
      Category.assoc, seedToOriginalKernel_snd, seedComparison_snd_assoc]

variable {Y : Scheme.{u}} (r : Y ⟶ D.left) (z : Y ⟶ pullback (a ≫ w) (a ≫ w))
  (hz : r ≫ pullback.lift p.left q.left h = z ≫ seedToOriginalKernel w a)

/-- Construct the full seed arrow from an original arrow above its coefficient kernel. -/
def squareLift : Y ⟶ doubleDomain p.left q.left a :=
  lift p.left q.left a r (z ≫ pullback.fst (a ≫ w) (a ≫ w))
    (z ≫ pullback.snd (a ≫ w) (a ≫ w))
    (by
      simpa only [Category.assoc, pullback.lift_fst, seedToOriginalKernel_fst] using
        congrArg (fun f ↦ f ≫ pullback.fst w w) hz)
    (by
      simpa only [Category.assoc, pullback.lift_snd, seedToOriginalKernel_snd] using
        congrArg (fun f ↦ f ≫ pullback.snd w w) hz)

@[reassoc]
theorem squareLift_arrow : squareLift w h a r z hz ≫ arrow p.left q.left a = r :=
  lift_arrow ..

@[reassoc]
theorem squareLift_comparison : squareLift w h a r z hz ≫ s = z := by
  apply pullback.hom_ext
  · rw [Category.assoc, seedComparison_fst, squareLift, lift_fst]
  · rw [Category.assoc, seedComparison_snd, squareLift, lift_snd]

include e in
/-- The complete seed comparison square is cartesian on arbitrary scheme tests. -/
theorem seedComparison_isPullback : IsPullback (arrow p.left q.left a) s m
    (seedToOriginalKernel w a) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (seedComparison_square w h a)
    (fun c ↦ squareLift w h a c.fst c.snd c.condition)
    (fun c ↦ squareLift_arrow w h a c.fst c.snd c.condition)
    (fun c ↦ squareLift_comparison w h a c.fst c.snd c.condition) ?_)
  intro c b _ hb
  apply SchemeRelationReanchoring.endpoint_ext e a
  · have H := congrArg (fun f ↦ f ≫ pullback.fst (a ≫ w) (a ≫ w)) hb
    simpa only [Category.assoc, seedComparison_fst, squareLift, lift_fst] using H
  · have H := congrArg (fun f ↦ f ≫ pullback.snd (a ≫ w) (a ≫ w)) hb
    simpa only [Category.assoc, seedComparison_snd, squareLift, lift_snd] using H

include e in
/-- Seed certificates are precisely the pullbacks of original kernel image certificates. -/
theorem mem_seed_image_iff (z : C) : z ∈ Set.range s ↔
    seedToOriginalKernel w a z ∈ Set.range m := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨arrow p.left q.left a d,
      congrArg (fun f ↦ f d) (seedComparison_square w h a)⟩
  · rintro ⟨d, hd⟩
    obtain ⟨c, _, hc⟩ := Scheme.exists_preimage_of_isPullback
      (seedComparison_isPullback e w h a) d z hd
    exact ⟨c, hc⟩

end FLT.Mazur.SchemeRelationSeedKernelTransport
