/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleDisjointSectionGluing
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Module sections on the specified coproduct over a base

Transport the scheme coproduct cover through the categorical comparison.
Its disjoint images allow arbitrary module sections to be prescribed independently.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Limits
namespace FLT.Mazur.FCurve
variable {S : Scheme.{u}} {ι : Type} (Y : ι → Over S)
/-- The specified coproduct over a base is covered by its actual inclusions. -/
@[implicit_reducible]
def overSigmaCover : (∐ Y).left.OpenCover :=
  ((sigmaOpenCover (fun i ↦ (Y i).left)).pushforwardIso
    (sigmaComparison (Over.forget S) Y)).copy ι (fun i ↦ (Y i).left)
      (fun i ↦ (Sigma.ι Y i).left) (Equiv.refl _) (fun _ ↦ Iso.refl _) (by
        intro i
        simp only [Iso.refl_hom, Category.id_comp,
          Scheme.Cover.pushforwardIso_f, sigmaOpenCover_f]
        exact (ι_comp_sigmaComparison (Over.forget S) Y i).symm)
/-- The actual inclusions in the over-category coproduct have disjoint open images. -/
lemma overSigmaCover_disjoint : Pairwise (fun i j ↦
    Disjoint ((overSigmaCover Y).f i ''ᵁ ⊤) ((overSigmaCover Y).f j ''ᵁ ⊤)) := by
  let (k : ι) : IsOpenImmersion (Sigma.ι Y k).left :=
    inferInstanceAs (IsOpenImmersion ((overSigmaCover Y).f k))
  intro i j hij
  change Disjoint ((Sigma.ι Y i).left ''ᵁ ⊤) ((Sigma.ι Y j).left ''ᵁ ⊤)
  have he (k : ι) : Sigma.ι (fun i ↦ (Y i).left) k ≫
      sigmaComparison (Over.forget S) Y = (Sigma.ι Y k).left :=
    ι_comp_sigmaComparison (Over.forget S) Y k
  simp only [Scheme.Hom.image_top_eq_opensRange]
  intro U hUi hUj x hx
  obtain ⟨a, rfl⟩ := hUi hx
  obtain ⟨b, hb⟩ := hUj hx
  have hab : Sigma.ι (fun k ↦ (Y k).left) j b = Sigma.ι (fun k ↦ (Y k).left) i a := by
    apply (sigmaComparison (Over.forget S) Y).homeomorph.injective
    change (Sigma.ι (fun k ↦ (Y k).left) j ≫ sigmaComparison (Over.forget S) Y) b =
      (Sigma.ι (fun k ↦ (Y k).left) i ≫ sigmaComparison (Over.forget S) Y) a
    simpa only [he, Over.forget_obj] using hb
  exact (hij (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hab)).symm).elim

/-- Arbitrary module sections on the over-category coproduct are component families. -/
lemma overSigma_sections_bijective (M : (∐ Y).left.Modules) :
    Function.Bijective (fun s : Γ(M, ⊤) ↦
      fun i ↦ pullGlobal ((overSigmaCover Y).f i) M s) :=
  pullGlobal_disjointCover_bijective (overSigmaCover Y) (overSigmaCover_disjoint Y) M
end FLT.Mazur.FCurve
