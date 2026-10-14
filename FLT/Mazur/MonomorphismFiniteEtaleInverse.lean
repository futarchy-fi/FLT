/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFppfImage
public import FLT.Mazur.EtaleFiniteBranchTargetNeighborhood

/-!
# Finite etale certificates for original inverse neighborhoods

A finite etale cover of an etale kernel neighborhood can lift to the original
relation without supplying an inverse on the kernel. Descent constructs that
inverse, with the complete nonreduced scheme structure. Conversely every point
of the inverse locus admits such a certificate inside any prescribed open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismOpenImage
set_option backward.isDefEq.respectTransparency false
variable {D K : Scheme.{u}} (m : D ⟶ K) [Mono m]

/-- A finite branch over an etale kernel neighborhood recovers the whole neighborhood image. -/
theorem etale_image_le_of_finite_cover {Z W : Scheme.{u}}
    (b : W ⟶ K) (t : Z ⟶ W) (a : Z ⟶ D)
    [Etale b] [Etale t] [Surjective t] (h : a ≫ m = t ≫ b) :
    Set.range b ⊆ (locus m : Set K) := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨z, rfl⟩ := t.surjective w
  exact fppf_image_le m (t ≫ b) a h ⟨z, rfl⟩

/-- Every inverse-locus point has an actual finite etale certificate in any target open. -/
theorem exists_finite_etale_certificate (x : K) (hx : x ∈ locus m)
    (U : K.Opens) (hU : x ∈ U) :
    ∃ (Z W : Scheme.{u}) (b : W ⟶ K) (t : Z ⟶ W) (a : Z ⟶ D) (z : Z),
      IsAffine Z ∧ IsAffine W ∧ Etale b ∧ Etale t ∧ IsFinite t ∧
        Surjective t ∧ a ≫ m = t ≫ b ∧ (t ≫ b) z = x ∧ Set.range b ⊆ U := by
  let X : Over K := Over.mk (locus m).ι
  let Y : Over K := Over.mk (𝟙 K)
  let f : X ⟶ Y := Over.homMk (locus m).ι (Category.comp_id _)
  let _ : Etale f.left := inferInstanceAs (Etale (locus m).ι)
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, _, he, hz, _, hΨ⟩ :=
    EtaleFiniteBranchTargetNeighborhood.exists_cover f ⊤ U ⟨x, hx⟩ (by trivial) hU
  have he' : a.left ≫ (locus m).ι = t.left ≫ b.left := congrArg Over.Hom.left he
  refine ⟨Z.left, W.left, b.left, t.left, a.left ≫ lift m, z,
    hZ, hW, hb, ht, hf, hs, ?_, ?_, hΨ⟩
  · rw [Category.assoc, lift_comp, he']
  · rw [← he']
    exact congrArg Subtype.val hz

/-- Finite etale neighborhood certificates detect the original inverse locus exactly. -/
theorem mem_locus_iff_finite_etale_certificate (x : K) : x ∈ locus m ↔
    ∃ (Z W : Scheme.{u}) (b : W ⟶ K) (t : Z ⟶ W) (a : Z ⟶ D) (z : Z),
      IsAffine Z ∧ IsAffine W ∧ Etale b ∧ Etale t ∧ IsFinite t ∧
        Surjective t ∧ a ≫ m = t ≫ b ∧ (t ≫ b) z = x := by
  constructor
  · intro hx
    obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, he, hz, _⟩ :=
      exists_finite_etale_certificate m x hx ⊤ (by trivial)
    exact ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, he, hz⟩
  · rintro ⟨Z, W, b, t, a, z, _, _, hb, ht, _, hs, he, hz⟩
    let _ := hb
    let _ := ht
    let _ := hs
    rw [← hz]
    exact etale_image_le_of_finite_cover m b t a he ⟨t z, rfl⟩

end FLT.Mazur.MonomorphismOpenImage
