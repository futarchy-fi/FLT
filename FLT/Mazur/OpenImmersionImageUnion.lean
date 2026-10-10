/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Covering unions of open immersion images

The union of a family of open images has a cover by the original source
schemes. This retains the literal overlap schemes when assembling an
ambient-chart intersection from several principal labels.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)]

/-- The open union of the images of the given embeddings. -/
def openImageUnion : X.Opens := ⨆ i, (f i).opensRange

/-- Each original overlap maps to the union of the ambient images. -/
def openImageUnionMap (i : ι) : V i ⟶ (openImageUnion f).toScheme :=
  IsOpenImmersion.lift (openImageUnion f).ι (f i) (by
    change (f i).opensRange ≤ (openImageUnion f).ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    exact le_iSup (fun i ↦ (f i).opensRange) i)

/-- The union inclusion recovers the original ambient embedding. -/
@[reassoc (attr := simp)] theorem openImageUnionMap_fac (i : ι) :
    openImageUnionMap f i ≫ (openImageUnion f).ι = f i :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every original overlap is open in the union. -/
instance openImageUnionMap_isOpenImmersion (i : ι) :
    IsOpenImmersion (openImageUnionMap f i) := by
  dsimp only [openImageUnionMap]
  infer_instance

/-- The union is covered by the original overlap schemes, without replacing their domains. -/
def openImageUnionCover : (openImageUnion f).toScheme.OpenCover where
  I₀ := ι
  X := V
  f := openImageUnionMap f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨i, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp z.2
    refine ⟨i, y, ?_⟩
    apply (openImageUnion f).ι.isOpenEmbedding.injective
    change ((openImageUnionMap f i ≫ (openImageUnion f).ι) y) = _
    rw [openImageUnionMap_fac]
    exact hy

end FLT.Mazur
