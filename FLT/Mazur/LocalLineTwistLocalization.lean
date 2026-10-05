/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionTwistRestriction
public import FLT.Mazur.TrivialLineTwistLocalization

/-!
# Finite-stage localization on a line-trivializing open

The section-level lifting and annihilation statements use the restrictions
of the ambient twist terms and maps. Only the line on the chosen open is
trivialized; the ambient line need not be trivial.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

open ModuleSheafTensor

variable {X Y : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
  [CompactSpace Y] [Y.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
  {L : X.Modules} (e : L.restrict j ≅ structureModule Y) (s : Γ(L, ⊤))

include e in
/-- Local denominators are cleared using the restrictions of the actual ambient maps. -/
theorem exists_restricted_stage_lift (n : ℕ)
    (b : Γ(((system M s).obj n).restrict j,
      sectionGeneratorOpen (L.restrict j) (restrictedSection j s))) :
    ∃ (d : ℕ) (t : Γ(((system M s).obj (n + d)).restrict j, ⊤)),
      (((system M s).obj (n + d)).restrict j).presheaf.map
          (sectionGeneratorOpen (L.restrict j) (restrictedSection j s)).leTop.op t =
        ((restrictFunctor j).map ((system M s).map
          (homOfLE (Nat.le_add_right n d)))).app
            (sectionGeneratorOpen (L.restrict j) (restrictedSection j s)) b := by
  let W := sectionGeneratorOpen (L.restrict j) (restrictedSection j s)
  let a := restrictionSystemIso j M s
  obtain ⟨d, t, ht⟩ := exists_stage_lift (M.restrict j) e (restrictedSection j s) n
    ((a.app n).hom.app W b)
  refine ⟨d, (a.app (n + d)).inv.app ⊤ t, ?_⟩
  apply (sectionsCongr (a.app (n + d)) W).injective
  change (a.app (n + d)).hom.app W
    ((((system M s).obj (n + d)).restrict j).presheaf.map W.leTop.op _) = _
  have hn := ConcreteCategory.congr_hom
    ((a.app (n + d)).hom.val.naturality W.leTop.op) ((a.app (n + d)).inv.app ⊤ t)
  change (a.app (n + d)).hom.app W
      ((((system M s).obj (n + d)).restrict j).presheaf.map W.leTop.op _) =
    ((system (M.restrict j) (restrictedSection j s)).obj (n + d)).presheaf.map
      W.leTop.op ((a.app (n + d)).hom.app ⊤ ((a.app (n + d)).inv.app ⊤ t)) at hn
  have hc : (a.app (n + d)).hom.app ⊤ ((a.app (n + d)).inv.app ⊤ t) = t :=
    (sectionsCongr (a.app (n + d)) ⊤).apply_symm_apply t
  rw [hn, hc]
  refine ht.trans ?_
  exact (congrArg (fun f ↦ f.app W b) (a.hom.naturality
    (homOfLE (Nat.le_add_right n d)))).symm

include e in
/-- A section vanishing on the local generator open dies under an ambient transition. -/
theorem exists_restricted_stage_annihilator (n : ℕ)
    (t : Γ(((system M s).obj n).restrict j, ⊤))
    (ht : (((system M s).obj n).restrict j).presheaf.map
      (sectionGeneratorOpen (L.restrict j) (restrictedSection j s)).leTop.op t = 0) :
    ∃ d : ℕ, ((restrictFunctor j).map ((system M s).map
      (homOfLE (Nat.le_add_right n d)))).app ⊤ t = 0 := by
  let W := sectionGeneratorOpen (L.restrict j) (restrictedSection j s)
  let a := restrictionSystemIso j M s
  have hz : ((system (M.restrict j) (restrictedSection j s)).obj n).presheaf.map
      W.leTop.op ((a.app n).hom.app ⊤ t) = 0 := by
    have hn := ConcreteCategory.congr_hom ((a.app n).hom.val.naturality W.leTop.op) t
    change (a.app n).hom.app W
        ((((system M s).obj n).restrict j).presheaf.map W.leTop.op t) = _ at hn
    refine hn.symm.trans ?_
    erw [ht, map_zero]
  obtain ⟨d, hd⟩ := exists_stage_annihilator (M.restrict j) e (restrictedSection j s) n
    ((a.app n).hom.app ⊤ t) hz
  refine ⟨d, (sectionsCongr (a.app (n + d)) ⊤).injective ?_⟩
  have hn := congrArg (fun f ↦ f.app ⊤ t)
    (a.hom.naturality (homOfLE (Nat.le_add_right n d)))
  change (a.app (n + d)).hom.app ⊤
    (((restrictFunctor j).map ((system M s).map (homOfLE (Nat.le_add_right n d)))).app ⊤ t) =
      (a.app (n + d)).hom.app ⊤ 0
  rw [map_zero]
  exact hn.trans hd

end FLT.Mazur.FCurve.LineSectionTwistSystem
