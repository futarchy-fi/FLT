/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# Isomorphisms between ambient image unions

A common family of overlap schemes embedded in two ambient charts identifies
the two image unions. Compatibility in both charts proves that the two glued
maps are inverse on the full unions, not just on individual principal patches.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) (g : ∀ i, V i ⟶ Y)
  [∀ i, IsOpenImmersion (f i)] [∀ i, IsOpenImmersion (g i)]
  (hg : ∀ i j, pullback.fst (f i) (f j) ≫ g i = pullback.snd (f i) (f j) ≫ g j)

include hg in
/-- Ambient compatibility persists after factoring the target maps through their union. -/
theorem openImageUnionMap_compatible (i j : ι) :
    pullback.fst (f i) (f j) ≫ openImageUnionMap g i =
      pullback.snd (f i) (f j) ≫ openImageUnionMap g j := by
  apply (cancel_mono (openImageUnion g).ι).mp
  simpa only [Category.assoc, openImageUnionMap_fac] using hg i j

/-- The common overlap family gives a map between its two ambient image unions. -/
def openImageUnionComparison : (openImageUnion f).toScheme ⟶ (openImageUnion g).toScheme :=
  openImageUnionGlue f (openImageUnionMap g) (openImageUnionMap_compatible f g hg)

/-- The union comparison identifies the two embeddings of each literal overlap. -/
@[reassoc (attr := simp)] theorem openImageUnionComparison_fac (i : ι) :
    openImageUnionMap f i ≫ openImageUnionComparison f g hg = openImageUnionMap g i :=
  openImageUnionGlue_fac f (openImageUnionMap g) (openImageUnionMap_compatible f g hg) i

variable
  (hf : ∀ i j, pullback.fst (g i) (g j) ≫ f i = pullback.snd (g i) (g j) ≫ f j)

/-- Opposite union comparisons compose to the identity on the full union. -/
theorem openImageUnionComparison_comp :
    openImageUnionComparison f g hg ≫ openImageUnionComparison g f hf = 𝟙 _ := by
  apply openImageUnion_hom_ext f
  intro i
  simp only [openImageUnionComparison_fac_assoc, openImageUnionComparison_fac, Category.comp_id]

/-- The full unions, with all original overlap identifications, are isomorphic. -/
def openImageUnionIso : (openImageUnion f).toScheme ≅ (openImageUnion g).toScheme where
  hom := openImageUnionComparison f g hg
  inv := openImageUnionComparison g f hf
  hom_inv_id := openImageUnionComparison_comp f g hg hf
  inv_hom_id := openImageUnionComparison_comp g f hf hg

/-- The isomorphism retains every original overlap map. -/
@[reassoc] theorem openImageUnionIso_fac (i : ι) :
    openImageUnionMap f i ≫ (openImageUnionIso f g hg hf).hom = openImageUnionMap g i :=
  openImageUnionComparison_fac f g hg i

/-- Swapping the two charts inverts their union isomorphism. -/
theorem openImageUnionIso_symm :
    (openImageUnionIso f g hg hf).symm = openImageUnionIso g f hf hg := rfl

end FLT.Mazur
