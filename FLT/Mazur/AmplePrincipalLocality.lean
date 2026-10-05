/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase
public import FLT.Mazur.PrincipalGeneratorExtension

/-!
# Principal-open locality of section ampleness

On a quasi-compact separated scheme, ampleness can be checked on a covering
by principal opens of global functions. Global numerators retain the original
affine generator opens, so no projective presentation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{0}} {L : X.Modules} [CompactSpace X] [X.IsSeparated]

/-- Section ampleness glues from principal neighborhoods of every point. -/
theorem ampleLineBundle_of_principal_neighborhoods (hL : LocallyFreeRankOne L)
    (h : ∀ x : X, ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧
      AmpleLineBundle (L.restrict (X.basicOpen r).ι)) : AmpleLineBundle L := by
  refine ⟨inferInstance, hL, fun x ↦ ?_⟩
  obtain ⟨r, hx, hA⟩ := h x
  let U := X.basicOpen r
  obtain ⟨n, hn, s, hs, haff⟩ := hA.2.2 ⟨x, hx⟩
  let e := tensorPowerRestrictIso L U.ι n
  let s' := e.inv.app ⊤ s
  have hopen : sectionGeneratorOpen ((tensorPower L n).restrict U.ι) s' =
      sectionGeneratorOpen (tensorPower (L.restrict U.ι) n) s :=
    sectionGeneratorOpen_iso e.symm s
  obtain ⟨t, ht⟩ := exists_principal_generator_extension (hL.tensorPower n) r U rfl s'
  refine ⟨n, hn, t, ?_, ?_⟩
  · rw [ht, hopen]
    exact ⟨⟨x, hx⟩, hs, rfl⟩
  · rw [ht, hopen]
    exact U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr haff

/-- A cover by ample principal restrictions certifies global ampleness. -/
theorem ampleLineBundle_iff_principal_neighborhoods (hL : LocallyFreeRankOne L) :
    AmpleLineBundle L ↔ ∀ x : X, ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧
      AmpleLineBundle (L.restrict (X.basicOpen r).ι) := by
  refine ⟨fun h x ↦ ⟨1, ?_, h.restrict_affine _⟩,
    ampleLineBundle_of_principal_neighborhoods hL⟩
  simp

end FLT.Mazur.FCurve
