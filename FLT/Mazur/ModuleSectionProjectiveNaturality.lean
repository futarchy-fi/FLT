/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionProjectiveChartNaturality
public import FLT.Mazur.ModuleSectionProjectiveGluing
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# The projective morphism of pulled-back line sections

The full projective morphism, including its coefficient map, commutes with
arbitrary scheme pullback. The proof compares actual normalized charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFreeRankOne M)
  {R : Type u} [CommRing R] (d : ℕ) (t : Fin (d + 1) → Γ(M, ⊤))
  (ht : (⨆ i, sectionGeneratorOpen M (t i)) = ⊤) (r : R →+* Γ(Y, ⊤))

include hM ht in
/-- Pullback preserves the original generating cover. -/
theorem sectionGeneratorCover_pullback :
    (⨆ i, sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t i))) = ⊤ := by
  simp only [sectionGeneratorOpen_pullGlobal hM, ← Scheme.Hom.preimage_iSup, ht,
    Scheme.Hom.preimage_top]

/-- The local coefficient map is the restriction of the actual pulled-back coefficient map. -/
theorem sectionChartScalars_pullback (U : Y.Opens) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V hV).hom.comp (sectionChartScalars r U) =
      sectionChartScalars (f.appTop.hom.comp r) V := by
  apply RingHom.ext
  intro a
  change f.appLE U V hV (Y.presheaf.map (homOfLE le_top).op (r a)) =
    X.presheaf.map (homOfLE le_top).op (f.appTop (r a))
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  have he := ConcreteCategory.congr_hom (f.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (r a)
  change f.app U (Y.presheaf.map (homOfLE le_top).op (r a)) =
    X.presheaf.map (homOfLE le_top).op (f.appTop (r a)) at he
  rw [he, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual glued projective morphism is unchanged by forming the pulled-back coordinates. -/
theorem sectionProjectiveMorphism_pullback :
    f ≫ sectionProjectiveMorphism M d t ht r =
      sectionProjectiveMorphism ((pullback f).obj M) d
        (fun i ↦ pullGlobal f M (t i)) (sectionGeneratorCover_pullback f M hM d t ht)
        (f.appTop.hom.comp r) := by
  apply (sectionGeneratorCover ((pullback f).obj M) d (fun i ↦ pullGlobal f M (t i))
    (sectionGeneratorCover_pullback f M hM d t ht)).hom_ext
  intro i
  let U := sectionGeneratorOpen M (t i)
  let V := sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t i))
  have hV : V ≤ f ⁻¹ᵁ U := (sectionGeneratorOpen_pullGlobal hM f (t i)).le
  change V.ι ≫ f ≫ _ = V.ι ≫ _
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hV, Category.assoc,
    sectionGeneratorOpen_ι_projectiveMorphism M d t ht r i,
    sectionGeneratorOpen_ι_projectiveMorphism ((pullback f).obj M) d
      (fun j ↦ pullGlobal f M (t j)) _ _ i]
  dsimp only [sectionProjectiveLocalMorphism]
  rw [sectionProjectiveChartMorphism_pullback f M d t i U V hV le_rfl le_rfl,
    sectionChartScalars_pullback]

end FLT.Mazur.FCurve
