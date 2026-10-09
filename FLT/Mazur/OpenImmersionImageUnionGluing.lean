/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion

/-!
# Gluing maps on unions of open images

Compatibility can be checked using pullbacks in the ambient scheme.
The resulting map on the union retains each original source map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {X T : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)]
  (g : ∀ i, V i ⟶ T)
  (hg : ∀ i j, pullback.fst (f i) (f j) ≫ g i = pullback.snd (f i) (f j) ≫ g j)

include hg in
/-- Ambient compatibility also holds on the intersections in the union. -/
theorem openImageUnion_compatible (i j : ι) :
    pullback.fst (openImageUnionMap f i) (openImageUnionMap f j) ≫ g i =
      pullback.snd (openImageUnionMap f i) (openImageUnionMap f j) ≫ g j := by
  let d : pullback (openImageUnionMap f i) (openImageUnionMap f j) ⟶
      pullback (f i) (f j) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
      rw [← openImageUnionMap_fac f i, ← openImageUnionMap_fac f j,
        ← Category.assoc, ← Category.assoc, pullback.condition])
  have h := congrArg (fun k ↦ d ≫ k) (hg i j)
  simpa only [Category.assoc, d, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h

/-- Glue compatible maps from the original overlaps over their ambient image union. -/
def openImageUnionGlue : (openImageUnion f).toScheme ⟶ T :=
  (openImageUnionCover f).glueMorphisms g (openImageUnion_compatible f g hg)

/-- The glued union map has its specified value on every original overlap. -/
@[reassoc (attr := simp)] theorem openImageUnionGlue_fac (i : ι) :
    openImageUnionMap f i ≫ openImageUnionGlue f g hg = g i :=
  (openImageUnionCover f).ι_glueMorphisms g (openImageUnion_compatible f g hg) i

/-- Maps on the entire union are determined by the original overlap schemes. -/
theorem openImageUnion_hom_ext (g h : (openImageUnion f).toScheme ⟶ T)
    (he : ∀ i, openImageUnionMap f i ≫ g = openImageUnionMap f i ≫ h) : g = h :=
  (openImageUnionCover f).hom_ext g h he

end FLT.Mazur
