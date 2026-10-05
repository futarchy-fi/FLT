/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionTwistCoordinates
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Finite-stage localization for a trivialized line

On a quasi-compact separated scheme, sections on the generator open lift
through the actual twist transitions at some finite stage. A section that
restricts to zero is killed by a finite transition. These are section-level
statements; global cohomological annihilation for a nontrivial line requires
combining them on a finite trivializing cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open Chow ModuleSheafTensor ModuleLineBundleTensorPullback

variable {X : Scheme} [CompactSpace X] [X.IsSeparated]
  (M : X.Modules) [M.IsQuasicoherent]

/-- A section vanishing on a principal open is killed by a finite scalar power. -/
theorem exists_principalSection_annihilator (r : Γ(X, ⊤))
    (W : X.Opens) (hW : W = X.basicOpen r) (t : Γ(M, ⊤))
    (ht : M.presheaf.map W.leTop.op t = 0) : ∃ n : ℕ, r ^ n • t = 0 := by
  have hρ : affineBaseScalars X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
    simp [affineBaseScalars, Scheme.toSpecΓ_appTop]
  have h := sectionBaseRestriction_isLocalized X.toSpecΓ M r
  rw [hρ, X.toSpecΓ_preimage_basicOpen r, ← hW] at h
  let := h
  let a := baseRestriction M (RingHom.id Γ(X, ⊤)) (show W ≤ ⊤ from le_top)
  have he : a t = a 0 := ht.trans (map_zero a).symm
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r he
  refine ⟨n, ?_⟩
  change X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op (r ^ n) • t =
    X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op (r ^ n) • (0 : Γ(M, ⊤)) at hn
  simpa using hn

namespace LineSectionTwistSystem

variable {L : X.Modules} (e : L ≅ structureModule X) (s : Γ(L, ⊤))

omit [CompactSpace X] [X.IsSeparated] [M.IsQuasicoherent] in
/-- Restriction commutes with the actual coordinate map at every twist stage. -/
lemma coordinates_restrict (n : ℕ) (W : X.Opens)
    (t : Γ(tensor M (tensorPower L n), ⊤)) :
    (coordinates M e n).hom.app W
        ((tensor M (tensorPower L n)).presheaf.map W.leTop.op t) =
      M.presheaf.map W.leTop.op ((coordinates M e n).hom.app ⊤ t) :=
  ConcreteCategory.congr_hom ((coordinates M e n).hom.val.naturality W.leTop.op) t

include e in
/-- Clearing denominators lifts a local section through a finite actual twist transition. -/
theorem exists_stage_lift (n : ℕ)
    (b : Γ((system M s).obj n, sectionGeneratorOpen L s)) :
    ∃ (d : ℕ) (t : Γ((system M s).obj (n + d), ⊤)),
      ((system M s).obj (n + d)).presheaf.map (sectionGeneratorOpen L s).leTop.op t =
        (((system M s).map (homOfLE (Nat.le_add_right n d))).app
          (sectionGeneratorOpen L s) b) := by
  let W := sectionGeneratorOpen L s
  let r : Γ(X, ⊤) := e.hom.app ⊤ s
  have hW : W = X.basicOpen r := by
    dsimp only [W, r]
    rw [← sectionGeneratorOpen_iso e, sectionGeneratorOpen_structure]
  obtain ⟨d, t, ht⟩ := exists_principalSection_numerator M r W hW
    ((coordinates M e n).hom.app W b)
  refine ⟨d, (coordinates M e (n + d)).inv.app ⊤ t, ?_⟩
  apply (sectionsCongr (coordinates M e (n + d)) W).injective
  change (coordinates M e (n + d)).hom.app W
    ((tensor M (tensorPower L (n + d))).presheaf.map W.leTop.op _) = _
  rw [coordinates_restrict]
  have hc : (coordinates M e (n + d)).hom.app ⊤
      ((coordinates M e (n + d)).inv.app ⊤ t) = t :=
    (sectionsCongr (coordinates M e (n + d)) ⊤).apply_symm_apply t
  rw [hc]
  exact ht.trans (map_coordinates M e s n d W b).symm

include e in
/-- A global section invisible on the generator open dies at a finite actual stage. -/
theorem exists_stage_annihilator (n : ℕ) (t : Γ((system M s).obj n, ⊤))
    (ht : ((system M s).obj n).presheaf.map (sectionGeneratorOpen L s).leTop.op t = 0) :
    ∃ d : ℕ, (((system M s).map (homOfLE (Nat.le_add_right n d))).app ⊤ t) = 0 := by
  let W := sectionGeneratorOpen L s
  let r : Γ(X, ⊤) := e.hom.app ⊤ s
  have hW : W = X.basicOpen r := by
    dsimp only [W, r]
    rw [← sectionGeneratorOpen_iso e, sectionGeneratorOpen_structure]
  have hz : M.presheaf.map W.leTop.op ((coordinates M e n).hom.app ⊤ t) = 0 := by
    rw [← coordinates_restrict]
    erw [ht, map_zero]
  obtain ⟨d, hd⟩ := exists_principalSection_annihilator M r W hW _ hz
  refine ⟨d, (sectionsCongr (coordinates M e (n + d)) ⊤).injective ?_⟩
  change (coordinates M e (n + d)).hom.app ⊤
    (((system M s).map (homOfLE (Nat.le_add_right n d))).app ⊤ t) =
      (coordinates M e (n + d)).hom.app ⊤ 0
  rw [map_coordinates, map_zero]
  change (X.presheaf.map (𝟙 _) r) ^ d • (coordinates M e n).hom.app ⊤ t = 0
  erw [CategoryTheory.Functor.map_id]
  exact hd

end LineSectionTwistSystem
end FLT.Mazur.FCurve
