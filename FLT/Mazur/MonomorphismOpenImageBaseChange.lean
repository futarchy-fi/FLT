/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFppfImage

/-!
# The inverse locus under actual flat base change

The largest open inverse locus commutes with flat, locally finitely presented
base change. In particular, genuine fppf refinements cannot manufacture inverse
neighborhoods absent from the original target. No reducedness is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismOpenImage
set_option backward.isDefEq.respectTransparency false
variable {D K D' K' : Scheme.{u}} (m : D ⟶ K) [Mono m]
  (a : D' ⟶ D) (m' : D' ⟶ K') (t : K' ⟶ K)
  (h : IsPullback a m' m t)

include h in
/-- Every actual inverse neighborhood pulls back to an inverse neighborhood. -/
theorem preimage_locus_le : t ⁻¹ᵁ locus m ≤ locus m' := by
  let U := t ⁻¹ᵁ locus m
  let b : U.toScheme ⟶ D := (t ∣_ locus m) ≫ lift m
  have hb : b ≫ m = U.ι ≫ t := by
    rw [Category.assoc, lift_comp, morphismRestrict_ι]
  let c := h.lift b U.ι hb
  exact le_locus m' U c (h.lift_snd _ _ _)

include h in
/-- Flat finite-presentation refinement detects precisely the original inverse open. -/
theorem locus_baseChange [Flat t] [LocallyOfFinitePresentation t] :
    locus m' = t ⁻¹ᵁ locus m := by
  apply le_antisymm
  · let _ : Mono m' := h.mono_snd_of_mono
    have e : (lift m' ≫ a) ≫ m = (locus m').ι ≫ t := by
      rw [Category.assoc, h.w, ← Category.assoc, lift_comp]
    intro x hx
    exact mem_locus_of_fppf_lift m ((locus m').ι ≫ t) (lift m' ≫ a) e ⟨x, hx⟩
  · exact preimage_locus_le m a m' t h

include h in
/-- The original locus is all of the target exactly when it is after an fppf cover. -/
theorem locus_top_iff_baseChange [Flat t] [LocallyOfFinitePresentation t] [Surjective t] :
    locus m' = ⊤ ↔ locus m = ⊤ := by
  rw [locus_baseChange m a m' t h]
  constructor
  · intro he
    apply top_le_iff.mp
    intro x _
    obtain ⟨y, rfl⟩ := t.surjective x
    have hy : y ∈ t ⁻¹ᵁ locus m := by rw [he]; trivial
    exact hy
  · intro he
    rw [he]
    rfl

/-- A globally invertible locus is an actual scheme isomorphism, not just a bijection. -/
theorem isIso_iff_locus_top : IsIso m ↔ locus m = ⊤ := by
  constructor
  · intro hm
    let _ := hm
    apply top_le_iff.mp
    exact le_locus m ⊤ ((⊤ : K.Opens).ι ≫ inv m) (by simp)
  · intro hm
    let e := K.topIso
    let b : K ⟶ D := e.inv ≫ K.homOfLE (by rw [hm]) ≫ lift m
    have hb : b ≫ m = 𝟙 K := by
      rw [Category.assoc, Category.assoc, lift_comp, Scheme.homOfLE_ι]
      exact e.inv_hom_id
    exact (sectionIso m b hb).isIso_hom

end FLT.Mazur.MonomorphismOpenImage
