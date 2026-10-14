/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring

/-!
# Quotient schemes constructed from representatives on a seed

The seed can be any scheme over the original parameter source. Original
arrows choose representatives inside that seed. Invariance is imposed on
its full two-coordinate relation, and constructs an idempotent endomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S B : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}

/-- Original representative arrows on a seed, with full scheme-level invariance. -/
structure Data (p q : D ⟶ A) (k : B ⟶ A.left) where
  /-- The representative endomorphism of the seed. -/
  rep : B ⟶ B
  /-- Actual original arrows from each parameter to its representative. -/
  arrow : B ⟶ D.left
  /-- Each arrow starts at the original parameter. -/
  source : arrow ≫ p.left = k
  /-- Each arrow ends at the chosen seed representative. -/
  target : arrow ≫ q.left = rep ≫ k
  /-- Both independent coordinates of the complete relation choose the same representative. -/
  invariant : fst p.left q.left k ≫ rep = snd p.left q.left k ≫ rep

namespace Data
variable {k : B ⟶ A.left} (d : Data p q k)

/-- Invariance applies to every original arrow with two seed lifts. -/
theorem on_arrow {Y : Scheme.{u}} (a : Y ⟶ D.left) (x y : Y ⟶ B)
    (hx : a ≫ p.left = x ≫ k) (hy : a ≫ q.left = y ≫ k) :
    x ≫ d.rep = y ≫ d.rep := by
  simpa only [← Category.assoc, lift_fst, lift_snd] using
    congrArg (fun z ↦ lift p.left q.left k a x y hx hy ≫ z) d.invariant

/-- The chosen representative is fixed, proved using its actual original arrow. -/
theorem idempotent : d.rep ≫ d.rep = d.rep := by
  exact (d.on_arrow d.arrow (𝟙 B) d.rep
    (by simpa only [Category.id_comp] using d.source) d.target).symm.trans
      (Category.id_comp _)

/-- The constructed scheme of representatives. -/
def quotient : Scheme.{u} := equalizer (𝟙 B) d.rep

/-- Its inclusion retains the full fixed scheme structure. -/
def inclusion : d.quotient ⟶ B := equalizer.ι (𝟙 B) d.rep

instance inclusion_mono : Mono d.inclusion :=
  inferInstanceAs (Mono (equalizer.ι (𝟙 B) d.rep))

/-- The seed projection is constructed by idempotence. -/
def projection : B ⟶ d.quotient :=
  equalizer.lift d.rep (by simpa only [Category.comp_id] using d.idempotent.symm)

@[reassoc]
theorem projection_inclusion : d.projection ≫ d.inclusion = d.rep := equalizer.lift_ι _ _

@[reassoc]
theorem inclusion_rep : d.inclusion ≫ d.rep = d.inclusion := by
  simpa only [Category.comp_id, inclusion] using (equalizer.condition (𝟙 B) d.rep).symm

@[reassoc]
theorem inclusion_projection : d.inclusion ≫ d.projection = 𝟙 d.quotient := by
  apply (cancel_mono d.inclusion).mp
  rw [Category.assoc, projection_inclusion, inclusion_rep, Category.id_comp]

instance projection_surjective : Surjective d.projection := ⟨fun x ↦
  ⟨d.inclusion x, congrArg (fun a ↦ a x) d.inclusion_projection⟩⟩

/-- The projection coequalizes the full original seed relation. -/
theorem condition : fst p.left q.left k ≫ d.projection =
    snd p.left q.left k ≫ d.projection := by
  apply (cancel_mono d.inclusion).mp
  simpa only [Category.assoc, projection_inclusion] using d.invariant

/-- Every invariant morphism descends to the constructed scheme. -/
@[reassoc]
theorem projection_descend {T : Scheme.{u}} (g : B ⟶ T)
    (hg : fst p.left q.left k ≫ g = snd p.left q.left k ≫ g) :
    d.projection ≫ d.inclusion ≫ g = g := by
  have h := congrArg (fun z ↦ lift p.left q.left k d.arrow (𝟙 B) d.rep
    (by simpa only [Category.id_comp] using d.source) d.target ≫ z) hg
  rw [projection_inclusion_assoc]
  simpa only [← Category.assoc, lift_fst, lift_snd, Category.id_comp] using h.symm

end Data
end FLT.Mazur.SchemeRelationSeedSelector
