/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteFreeAtlas

/-!
# The locally directed affine free cover

Local finite freeness supplies a covering diagram of actual affine free opens.
The diagram is locally directed, and its canonical cocone has colimit the base
scheme itself. Its transition maps are the ordinary open inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFiniteFreeAtlas
open FCurve
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)

/-- The covering family of all actual affine free opens. -/
def cover : X.OpenCover where
  I₀ := Index M
  X i := i.val.toScheme
  f i := i.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi, _⟩ := exists_mem_le M hM (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

instance : PartialOrder (cover M hM).I₀ := inferInstanceAs (PartialOrder (Index M))

/-- The affine free cover is directed locally on every overlap. -/
instance coverLocallyDirected : (cover M hM).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp [cover]) <| by
    convert isBasis M hM using 1
    simp [cover]

/-- The atlas transition maps are the actual inclusions of affine opens. -/
@[simp]
lemma cover_trans {i j : Index M} (h : i ≤ j) :
    (cover M hM).trans (homOfLE h) = X.homOfLE h := rfl

/-- The canonical affine free diagram has the original base as its colimit. -/
def baseIsColimit : IsColimit (cover M hM).coconeOfLocallyDirected :=
  (cover M hM).isColimitCoconeOfLocallyDirected

/-- The abstract colimit of the affine free base diagram is the original scheme. -/
def baseIso : colimit (cover M hM).functorOfLocallyDirected ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (baseIsColimit M hM)

/-- The colimit identification preserves each actual affine open inclusion. -/
@[reassoc (attr := simp)]
lemma baseIso_chart (i : Index M) :
    colimit.ι (cover M hM).functorOfLocallyDirected i ≫ (baseIso M hM).hom = i.val.ι :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (baseIsColimit M hM) i

end FLT.Mazur.AffineFiniteFreeAtlas
