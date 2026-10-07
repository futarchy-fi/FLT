/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom
public import FLT.Mazur.ModuleSheafPullbackIsoDetection

/-!
# Gluing actual pullback morphisms on open-immersion covers

Compatible pullback maps glue uniquely to a global linear morphism.
The result recovers the supplied maps as actual pullbacks, and local
isomorphisms give a global isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u v

namespace FLT.Mazur.ModuleSheafOpenImmersionGluing

open ModuleSheafOpenImmersionLocalHom

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v}
variable (Y : ι → Scheme.{u}) (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (hcover : ∀ x : X, ∃ j, x ∈ Set.range (i j))

include hcover in
/-- The images of a jointly surjective family of open immersions cover the scheme. -/
lemma iSup_opensRange : ⨆ j, (i j).opensRange = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨j, hj⟩ := hcover x
  exact Opens.mem_iSup.mpr ⟨j, hj⟩

include hcover in
/-- Equality of module morphisms is detected by open-immersion pullbacks. -/
lemma hom_ext (a b : M ⟶ N)
    (h : ∀ j, (pullback (i j)).map a = (pullback (i j)).map b) : a = b := by
  apply ModuleSheafMorphismGluing.hom_ext (fun j ↦ (i j).opensRange)
    (iSup_opensRange Y i hcover)
  intro j
  simpa only [localHom_map] using congrArg (localHom (i j)) (h j)

variable (a : ∀ j, (pullback (i j)).obj M ⟶ (pullback (i j)).obj N)

/-- Compatibility is equality of the induced linear maps on all overlap subopens. -/
def Compatible : Prop :=
  ModuleSheafMorphismGluing.Compatible (fun j ↦ (i j).opensRange)
    (fun j ↦ localHom (i j) (a j))

variable (ha : Compatible Y i a)

include hcover ha in
/-- Actual pullback maps satisfying the local overlap condition glue uniquely. -/
theorem existsUnique_glue :
    ∃! b : M ⟶ N, ∀ j, (pullback (i j)).map b = a j := by
  obtain ⟨b, hb, _⟩ := ModuleSheafMorphismGluing.existsUnique_glue
    (fun j ↦ (i j).opensRange) (iSup_opensRange Y i hcover)
    (fun j ↦ localHom (i j) (a j)) ha
  have hb' (j) : (pullback (i j)).map b = a j := by
    apply localHom_injective (i j)
    rw [localHom_map, hb]
  exact ⟨b, hb', fun c hc ↦ hom_ext Y i hcover c b (fun j ↦ (hc j).trans (hb' j).symm)⟩

/-- The global linear morphism obtained by gluing the supplied pullback maps. -/
def glue : M ⟶ N := (existsUnique_glue Y i hcover a ha).exists.choose

/-- The glued morphism recovers each original pullback map exactly. -/
lemma pullback_glue (j : ι) : (pullback (i j)).map (glue Y i hcover a ha) = a j :=
  (existsUnique_glue Y i hcover a ha).exists.choose_spec j

/-- A glued morphism of locally invertible maps is itself invertible. -/
lemma glue_isIso (hiso : ∀ j, IsIso (a j)) : IsIso (glue Y i hcover a ha) := by
  apply ModuleSheafPullbackIsoDetection.isIso_of_openImmersionPullbacks
    (glue Y i hcover a ha) Y i hcover
  intro j
  rw [pullback_glue]
  exact hiso j

/-- Glue local isomorphisms while retaining their original pullback morphisms. -/
def glueIso (hiso : ∀ j, IsIso (a j)) : M ≅ N :=
  let _ := glue_isIso Y i hcover a ha hiso
  asIso (glue Y i hcover a ha)

end FLT.Mazur.ModuleSheafOpenImmersionGluing
