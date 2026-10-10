/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyTripleChart

/-!
# The original triples cover the total family triple overlap

The original adjacent-pair triple charts form a disjoint open cover. Their
actual coproduct is isomorphic to the total triple overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The cover consists precisely of triples of original members. -/
def tripleCover : (SchemeTripleOverlap.triple (projection 𝒰)).OpenCover :=
  ((Scheme.Pullback.openCoverOfLeftRight (pairCover 𝒰) (sigmaOpenCover 𝒰.X)
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰) ≫ projection 𝒰)
    (projection 𝒰)).pushforwardIso
      (SchemeFamilyTripleOverlap.pasteIso
      (projection 𝒰) (projection 𝒰) (projection 𝒰)).inv).copy
    ((𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) (tripleChart 𝒰) (tripleChartMap 𝒰) (Equiv.refl _)
    (fun ijk ↦ SchemeFamilyTripleOverlap.pasteIso
      (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) ≪≫
        Limits.pullback.congrHom (pairMap_base 𝒰 ijk.1).symm
          (inclusion_projection 𝒰 ijk.2).symm) (by
      intro ijk
      dsimp only [Scheme.Cover.pushforwardIso_f, Scheme.Pullback.openCoverOfLeftRight_f,
        Iso.trans_hom, tripleChartMap]
      simp only [Category.assoc]
      congr 1
      rw [← Category.assoc]
      apply (cancel_mono (SchemeFamilyTripleOverlap.pasteIso
        (projection 𝒰) (projection 𝒰) (projection 𝒰)).inv).mpr
      apply Limits.pullback.hom_ext <;>
        simp [Limits.pullback.congrHom, Limits.pullback.map, pairCover])

/-- Every total triple lies in one of the original triple charts. -/
lemma tripleChartMap_covers : iSup (fun ijk ↦ (tripleChartMap 𝒰 ijk).opensRange) = ⊤ :=
  (tripleCover 𝒰).iSup_opensRange

/-- The original triple charts are jointly surjective. -/
lemma tripleChart_jointly_covers (x : SchemeTripleOverlap.triple (projection 𝒰)) :
    ∃ ijk, x ∈ Set.range (tripleChartMap 𝒰 ijk) := by
  have hx : x ∈ iSup (fun ijk ↦ (tripleChartMap 𝒰 ijk).opensRange) := by
    rw [tripleChartMap_covers]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- Distinct triples of member indices have disjoint images. -/
lemma tripleChartMap_disjoint : Pairwise (fun ijk lmn ↦
    Disjoint (tripleChartMap 𝒰 ijk).opensRange (tripleChartMap 𝒰 lmn).opensRange) := by
  intro ijk lmn h V hi hj x hx
  obtain ⟨a, ha⟩ := hi hx
  obtain ⟨b, hb⟩ := hj hx
  have h₁ := congrArg (SchemeTripleOverlap.coord1 (projection 𝒰)) (ha.trans hb.symm)
  have h₂ := congrArg (SchemeTripleOverlap.coord2 (projection 𝒰)) (ha.trans hb.symm)
  have h₃ := congrArg (SchemeTripleOverlap.coord3 (projection 𝒰)) (ha.trans hb.symm)
  change (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord1 _) a =
    (tripleChartMap 𝒰 lmn ≫ SchemeTripleOverlap.coord1 _) b at h₁
  change (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord2 _) a =
    (tripleChartMap 𝒰 lmn ≫ SchemeTripleOverlap.coord2 _) b at h₂
  change (tripleChartMap 𝒰 ijk ≫ SchemeTripleOverlap.coord3 _) a =
    (tripleChartMap 𝒰 lmn ≫ SchemeTripleOverlap.coord3 _) b at h₃
  rw [tripleChartMap_coord1, tripleChartMap_coord1] at h₁
  rw [tripleChartMap_coord2, tripleChartMap_coord2] at h₂
  rw [tripleChartMap_coord3, tripleChartMap_coord3] at h₃
  have e₁ := congrArg Sigma.fst ((sigmaι_eq_iff 𝒰.X _ _ _ _).mp h₁)
  have e₂ := congrArg Sigma.fst ((sigmaι_eq_iff 𝒰.X _ _ _ _).mp h₂)
  have e₃ := congrArg Sigma.fst ((sigmaι_eq_iff 𝒰.X _ _ _ _).mp h₃)
  exact (h (Prod.ext (Prod.ext e₁ e₂) e₃)).elim

/-- The total triple overlap is the coproduct of the original triple overlaps. -/
def tripleCoproductIso :
    (∐ tripleChart 𝒰) ≅ SchemeTripleOverlap.triple (projection 𝒰) := by
  have hc := nonempty_isColimit_cofanMk_of (tripleChartMap 𝒰)
    (tripleChartMap_covers 𝒰) (tripleChartMap_disjoint 𝒰)
  let _ : IsIso (Limits.Sigma.desc (tripleChartMap 𝒰)) :=
    (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk _ (tripleChartMap 𝒰))).mp hc
  exact asIso (Limits.Sigma.desc (tripleChartMap 𝒰))

/-- The comparison retains each original triple inclusion. -/
@[reassoc (attr := simp)]
lemma tripleCoproductIso_inclusion (ijk : (𝒰.I₀ × 𝒰.I₀) × 𝒰.I₀) :
    Limits.Sigma.ι (tripleChart 𝒰) ijk ≫ (tripleCoproductIso 𝒰).hom =
      tripleChartMap 𝒰 ijk := Limits.Sigma.ι_comp_desc _ _

end FLT.Mazur.SchemeFppfFamily
