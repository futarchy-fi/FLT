/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalLineTwistLocalization

/-!
# Ambient section localization on affine trivializing charts

Local finite-stage lifting and kernel annihilation are transported to the
ambient opens used by the direct-image Cech complex. Both statements retain
the actual section-twist maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

variable {X : Scheme} (M : X.Modules) [M.IsQuasicoherent]
  {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
  (V : X.Opens) (hV : IsAffineOpen V) (e : L.restrict V.ι ≅ structureModule V.toScheme)

/-- The direct-image evaluation open on a chart. -/
abbrev intersectionOpen : X.Opens :=
  (sectionGeneratorOpen L s).ι ''ᵁ ((sectionGeneratorOpen L s).ι ⁻¹ᵁ V)

include hL in
/-- The local generator open has exactly the ambient direct-image evaluation open. -/
lemma localGenerator_image :
    V.ι ''ᵁ sectionGeneratorOpen (L.restrict V.ι) (restrictedSection V.ι s) =
      intersectionOpen s V := by
  rw [show sectionGeneratorOpen (L.restrict V.ι) (restrictedSection V.ι s) =
      V.ι ⁻¹ᵁ sectionGeneratorOpen L s from sectionGeneratorOpen_restrict hL V.ι s]
  simp only [intersectionOpen, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm]

include hL hV e in
/-- Clearing a denominator lifts an actual ambient section on the chart intersection. -/
theorem exists_affine_stage_lift (n : ℕ)
    (b : Γ((system M s).obj n, intersectionOpen s V)) :
    ∃ (d : ℕ) (t : Γ((system M s).obj (n + d), V)),
      ((system M s).obj (n + d)).presheaf.map
          (homOfLE ((sectionGeneratorOpen L s).ι.image_preimage_le V)).op t =
        ((system M s).map (homOfLE (Nat.le_add_right n d))).app (intersectionOpen s V) b := by
  let : IsAffine V.toScheme := hV
  let W := sectionGeneratorOpen (L.restrict V.ι) (restrictedSection V.ι s)
  have hTop : V.ι ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hW : V.ι ''ᵁ W = intersectionOpen s V := localGenerator_image hL s V
  let b' : Γ(((system M s).obj n).restrict V.ι, W) :=
    ((system M s).obj n).presheaf.map (eqToHom hW).op b
  obtain ⟨d, t, ht⟩ := exists_restricted_stage_lift V.ι M e s n b'
  refine ⟨d, ((system M s).obj (n + d)).presheaf.map (eqToHom hTop.symm).op t, ?_⟩
  let A := (system M s).obj (n + d)
  let f := (system M s).map (homOfLE (Nat.le_add_right n d))
  apply (ConcreteCategory.bijective_of_isIso (A.presheaf.map (eqToHom hW).op)).injective
  change A.presheaf.map (eqToHom hW).op
      (A.presheaf.map _ (A.presheaf.map (eqToHom hTop.symm).op t)) =
    A.presheaf.map (eqToHom hW).op (f.app (intersectionOpen s V) b)
  have hn := ConcreteCategory.congr_hom (f.val.naturality (eqToHom hW).op) b
  change f.app (V.ι ''ᵁ W) (((system M s).obj n).presheaf.map (eqToHom hW).op b) =
    A.presheaf.map (eqToHom hW).op (f.app (intersectionOpen s V) b) at hn
  refine Eq.trans ?_ (ht.trans hn)
  change A.presheaf.map _ (A.presheaf.map _ (A.presheaf.map _ t)) =
    A.presheaf.map _ t
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

include hL hV e in
/-- An ambient section invisible on the intersection dies under an actual ambient transition. -/
theorem exists_affine_stage_annihilator (n : ℕ) (t : Γ((system M s).obj n, V))
    (ht : ((system M s).obj n).presheaf.map
      (homOfLE ((sectionGeneratorOpen L s).ι.image_preimage_le V)).op t = 0) :
    ∃ d : ℕ, ((system M s).map (homOfLE (Nat.le_add_right n d))).app V t = 0 := by
  let : IsAffine V.toScheme := hV
  let W := sectionGeneratorOpen (L.restrict V.ι) (restrictedSection V.ι s)
  have hTop : V.ι ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hW : V.ι ''ᵁ W = intersectionOpen s V := localGenerator_image hL s V
  let A := (system M s).obj n
  let t' : Γ(A.restrict V.ι, ⊤) := A.presheaf.map (eqToHom hTop).op t
  have hz : (A.restrict V.ι).presheaf.map W.leTop.op t' = 0 := by
    have he : (A.restrict V.ι).presheaf.map W.leTop.op t' =
        A.presheaf.map (eqToHom hW).op
          (A.presheaf.map (homOfLE ((sectionGeneratorOpen L s).ι.image_preimage_le V)).op t) := by
      change A.presheaf.map _ (A.presheaf.map _ t) = A.presheaf.map _ (A.presheaf.map _ t)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp]
      rfl
    rw [he, ht, map_zero]
  obtain ⟨d, hd⟩ := exists_restricted_stage_annihilator V.ι M e s n t' hz
  refine ⟨d, ?_⟩
  let B := (system M s).obj (n + d)
  let f := (system M s).map (homOfLE (Nat.le_add_right n d))
  apply (ConcreteCategory.bijective_of_isIso (B.presheaf.map (eqToHom hTop).op)).injective
  change B.presheaf.map (eqToHom hTop).op (f.app V t) = B.presheaf.map (eqToHom hTop).op 0
  rw [map_zero]
  have hn := ConcreteCategory.congr_hom (f.val.naturality (eqToHom hTop).op) t
  exact hn.symm.trans hd

end FLT.Mazur.FCurve.LineSectionTwistSystem
