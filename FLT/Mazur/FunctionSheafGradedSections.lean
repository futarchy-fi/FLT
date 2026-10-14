/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinePullbackAdjunction
public import FLT.Mazur.SectionGradedLinePullback

/-!
# Section algebras along a morphism preserving the structure sheaf

The original adjunction unit gives bijections in every tensor degree. The
existing multiplication-compatible pullback therefore gives a ring isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FunctionSheafGradedSections
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y : Scheme} (f : X ⟶ Y) [IsIso (StructureDirectImage.unitMap f)]
  {L : Y.Modules} {M : X.Modules} (hL : LocallyFreeRankOne L)
  (e : (pullback f).obj L ≅ M)

include hL

/-- The actual tensor-degree section map is an isomorphism of module sheaves. -/
theorem powerMap_isIso (n : ℕ) : IsIso (SectionGradedLinePullback.powerMap f e n) := by
  let _ := LinePullbackAdjunction.unit_isIso f (hL.tensorPower n)
  change IsIso (((pullbackPushforwardAdjunction f).unit.app (tensorPower L n) ≫
    (pushforward f).map (tensorPowerIso f L n).hom) ≫
      (pushforward f).map (tensorPowerCongr e n).hom)
  infer_instance

/-- Every local homogeneous section descends uniquely along the original comparison. -/
theorem sectionMap_bijective (n : ℕ) (U : Y.Opens) :
    Function.Bijective (SectionGradedLinePullback.sectionMap f e n U) := by
  let _ := powerMap_isIso f hL e n
  exact ConcreteCategory.bijective_of_isIso
    ((SectionGradedLinePullback.powerMap f e n).app U)

/-- The actual pullback on the full section ring is bijective in all degrees together. -/
theorem ringHom_bijective : Function.Bijective (SectionGradedLinePullback.ringHom f e) := by
  let E (n : ℕ) : Piece L ⊤ n ≃+ Piece M ⊤ n :=
    AddEquiv.ofBijective ((SectionGradedLinePullback.powerMap f e n).app ⊤).hom
      (sectionMap_bijective f hL e n ⊤)
  have he : (SectionGradedLinePullback.ringHom f e).toAddMonoidHom =
      (DirectSum.congrAddEquiv E).toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro n s
    change SectionGradedLinePullback.ringHom f e (SectionGradedSum.of L ⊤ n s) = _
    rw [SectionGradedLinePullback.ringHom_of]
    change _ = DirectSum.map (fun j ↦ (E j).toAddMonoidHom) (DirectSum.of _ n s)
    rw [DirectSum.map_of]
    rfl
  change Function.Bijective (SectionGradedLinePullback.ringHom f e).toAddMonoidHom
  rw [he]
  exact (DirectSum.congrAddEquiv E).bijective

/-- The section-ring isomorphism is the actual pullback, with the specified line transport. -/
def ringEquiv : SectionGradedSum.Sections L ⊤ ≃+* SectionGradedSum.Sections M ⊤ :=
  RingEquiv.ofBijective (SectionGradedLinePullback.ringHom f e) (ringHom_bijective f hL e)

/-- The ring equivalence retains every original homogeneous section pullback. -/
theorem ringEquiv_of (n : ℕ) (s : Piece L ⊤ n) :
    ringEquiv f hL e (SectionGradedSum.of L ⊤ n s) =
      SectionGradedSum.of M ⊤ n (SectionGradedLinePullback.sectionMap f e n ⊤ s) :=
  SectionGradedLinePullback.ringHom_of f e n s

/-- The equivalence carries each entire homogeneous piece onto its original degree. -/
theorem ringEquiv_grade (n : ℕ) :
    (ringEquiv f hL e) '' (SectionGradedSum.grade L ⊤ n : Set _) =
      (SectionGradedSum.grade M ⊤ n : Set _) := by
  ext s
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (ringEquiv_of f hL e n t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨a, ha⟩ := (sectionMap_bijective f hL e n ⊤).surjective t
    refine ⟨SectionGradedSum.of L ⊤ n a, ⟨a, rfl⟩, ?_⟩
    rw [ringEquiv_of, ha]

end FLT.Mazur.FunctionSheafGradedSections
