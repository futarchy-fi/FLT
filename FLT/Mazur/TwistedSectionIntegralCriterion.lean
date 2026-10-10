/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionPushforwardNaturality
public import FLT.Mazur.NonzeroLineSectionExact
public import FLT.Mazur.CartierTensorRank

/-!
# The integral-fiber nonvanishing criterion

On an integral total space, regularity of a line section is equivalent to
nonvanishing. Tensor duality and adjunction express this as nonvanishing of
the actual dual-base-line morphism into the direct image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
variable {X S : Scheme.{u}}

/-- The zero global section induces the zero sheaf morphism. -/
lemma globalSectionHom_zero (L : X.Modules) : globalSectionHom L 0 = 0 := by
  apply globalSection_hom_ext
  exact globalSectionHom_top L 0

/-- A regular section on a nonempty scheme cannot vanish identically. -/
theorem globalSection_ne_zero_of_mono [Nonempty X] (L : X.Modules) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] : s ≠ 0 := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice ‹Nonempty X›, trivial⟩⟩
  intro hs
  have hz : globalSectionHom L s = 0 := by rw [hs, globalSectionHom_zero]
  have hid : (𝟙 (structureModule X)) = 0 :=
    (cancel_mono (globalSectionHom L s)).mp (by simp only [hz, Limits.comp_zero])
  have h := congrArg (fun a : structureModule X ⟶ structureModule X ↦
    a.app ⊤ (1 : Γ(X, ⊤))) hid
  exact (one_ne_zero : (1 : Γ(X, ⊤)) ≠ 0) h

/-- On an integral scheme, nonvanishing is the complete regularity criterion for a line. -/
theorem integral_lineSection_regular_iff {Y : Scheme.{0}} [IsIntegral Y]
    (L : Y.Modules) (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) :
    Mono (globalSectionHom L s) ↔ s ≠ 0 :=
  ⟨fun _ ↦ globalSection_ne_zero_of_mono L s, nonzero_globalSectionHom_mono hL s⟩

/-- For an integral total space, the direct-image morphism detects regular twisted sections. -/
theorem integral_twistedSection_regular_iff {Y T : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ T) (L : Y.Modules) (hL : LocallyFreeRankOne L)
    {B : T.Modules} (hB : LocallyFreeRankOne B)
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    Mono (globalSectionHom (tensor L ((pullback f).obj B)) s) ↔
      twistedSectionPushforwardEquiv f L hB s ≠ 0 := by
  rw [twistedSectionPushforwardEquiv_ne_zero_iff]
  exact integral_lineSection_regular_iff _ (hL.tensor (hB.pullback f)) s

end FLT.Mazur.FCurve
