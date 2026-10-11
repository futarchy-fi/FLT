/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfSheafCriterion
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Fppf descent for local subfunctors on the big relative site

A subfunctor of a sheaf is a sheaf if membership is detected by the
original jointly surjective fppf covering families of test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemePicard
universe v
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- A sheaf satisfies descent for each original base covering family. -/
theorem relativeFppf_family_isSheafFor
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left) :
    Presieve.IsSheafFor F
      (Presieve.ofArrows (relativeCoverMember T 𝒰) (relativeCoverArrow T 𝒰)) := by
  rw [isSheaf_iff_isSheaf_of_type] at hF
  rw [Presieve.isSheafFor_iff_generate]
  apply hF
  rw [GrothendieckTopology.mem_over_iff, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck 𝒰.mem₀

/-- Local membership lets ambient amalgamations descend inside the subfunctor. -/
theorem relativeFppf_subfunctor_isSheaf (G : Subfunctor F)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : ∀ (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
      (c : F.obj (op T)),
      (∀ i, F.map (relativeCoverArrow T 𝒰 i).op c ∈
        G.obj (op (relativeCoverMember T 𝒰 i))) → c ∈ G.obj (op T)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G.toFunctor := by
  apply relativeFppf_isSheaf_of_families
  intro T 𝒰
  have h := relativeFppf_family_isSheafFor hF T 𝒰
  rw [Presieve.isSheafFor_arrows_iff] at h ⊢
  intro a ha
  obtain ⟨c, hc, hu⟩ := h (fun i ↦ (a i).val)
    (fun i j V p q hpq ↦ congrArg Subtype.val (ha i j V p q hpq))
  have hcG : c ∈ G.obj (op T) := hG T 𝒰 c (fun i ↦ (hc i).symm ▸ (a i).property)
  refine ⟨⟨c, hcG⟩, fun i ↦ Subtype.ext (hc i), ?_⟩
  intro b hb
  exact Subtype.ext (hu b.val (fun i ↦ congrArg Subtype.val (hb i)))

end FLT.Mazur.SchemePicard
