/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCover
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Original pairwise overlaps cover the coproduct overlap

The fiber products of the original covering maps form an open cover of the
actual double overlap of the coproduct covering morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- A pairwise overlap uses the original, potentially unequal, covering maps. -/
abbrev pair (ij : 𝒰.I₀ × 𝒰.I₀) : Scheme.{u} := Limits.pullback (𝒰.f ij.1) (𝒰.f ij.2)

/-- The original pairwise overlap maps to the double overlap of the coproduct. -/
def pairMap (ij : 𝒰.I₀ × 𝒰.I₀) :
    pair 𝒰 ij ⟶ Limits.pullback (projection 𝒰) (projection 𝒰) :=
  Limits.pullback.map _ _ _ _ (Limits.Sigma.ι 𝒰.X ij.1) (Limits.Sigma.ι 𝒰.X ij.2)
    (𝟙 X) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pairMap_fst (ij : 𝒰.I₀ × 𝒰.I₀) :
    pairMap 𝒰 ij ≫ Limits.pullback.fst (projection 𝒰) (projection 𝒰) =
      Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.1 :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairMap_snd (ij : 𝒰.I₀ × 𝒰.I₀) :
    pairMap 𝒰 ij ≫ Limits.pullback.snd (projection 𝒰) (projection 𝒰) =
      Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.2 :=
  Limits.pullback.lift_snd _ _ _

instance pairMap_isOpenImmersion (ij : 𝒰.I₀ × 𝒰.I₀) : IsOpenImmersion (pairMap 𝒰 ij) := by
  unfold pairMap
  infer_instance

/-- The cover has exactly the original pairwise fiber products as its members. -/
def pairCover : (Limits.pullback (projection 𝒰) (projection 𝒰)).OpenCover :=
  (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover 𝒰.X) (sigmaOpenCover 𝒰.X)
    (projection 𝒰) (projection 𝒰)).copy (𝒰.I₀ × 𝒰.I₀) (pair 𝒰) (pairMap 𝒰)
    (Equiv.refl _) (fun ij ↦ Limits.pullback.congrHom
      (inclusion_projection 𝒰 ij.1).symm (inclusion_projection 𝒰 ij.2).symm) (by
      intro ij
      apply Limits.pullback.hom_ext <;>
        simp [pairMap, Limits.pullback.map, Limits.pullback.congrHom])

/-- Every point of the total double overlap lies in an original pairwise overlap. -/
lemma pairMap_covers : iSup (fun ij ↦ (pairMap 𝒰 ij).opensRange) = ⊤ :=
  (pairCover 𝒰).iSup_opensRange

/-- Distinct ordered pairs define disjoint open charts on the total overlap. -/
lemma pairMap_disjoint :
    Pairwise (fun ij kl ↦ Disjoint (pairMap 𝒰 ij).opensRange (pairMap 𝒰 kl).opensRange) := by
  intro ij kl h V hi hj x hx
  obtain ⟨a, ha⟩ := hi hx
  obtain ⟨b, hb⟩ := hj hx
  have hf := congrArg (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (ha.trans hb.symm)
  have hs := congrArg (Limits.pullback.snd (projection 𝒰) (projection 𝒰))
    (ha.trans hb.symm)
  change (pairMap 𝒰 ij ≫ Limits.pullback.fst _ _) a =
    (pairMap 𝒰 kl ≫ Limits.pullback.fst _ _) b at hf
  change (pairMap 𝒰 ij ≫ Limits.pullback.snd _ _) a =
    (pairMap 𝒰 kl ≫ Limits.pullback.snd _ _) b at hs
  rw [pairMap_fst, pairMap_fst] at hf
  rw [pairMap_snd, pairMap_snd] at hs
  have h₁ := congrArg Sigma.fst ((sigmaι_eq_iff 𝒰.X _ _ _ _).mp hf)
  have h₂ := congrArg Sigma.fst ((sigmaι_eq_iff 𝒰.X _ _ _ _).mp hs)
  exact (h (Prod.ext h₁ h₂)).elim

/-- The total double overlap is the actual coproduct of the original pairwise overlaps. -/
def pairCoproductIso :
    (∐ pair 𝒰) ≅ Limits.pullback (projection 𝒰) (projection 𝒰) := by
  have hc := nonempty_isColimit_cofanMk_of (pairMap 𝒰)
    (pairMap_covers 𝒰) (pairMap_disjoint 𝒰)
  let _ : IsIso (Limits.Sigma.desc (pairMap 𝒰)) :=
    (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk _ (pairMap 𝒰))).mp hc
  exact asIso (Limits.Sigma.desc (pairMap 𝒰))

/-- The coproduct comparison retains each original pairwise chart. -/
@[reassoc (attr := simp)]
lemma pairCoproductIso_inclusion (ij : 𝒰.I₀ × 𝒰.I₀) :
    Limits.Sigma.ι (pair 𝒰) ij ≫ (pairCoproductIso 𝒰).hom = pairMap 𝒰 ij :=
  Limits.Sigma.ι_comp_desc _ _

end FLT.Mazur.SchemeFppfFamily
