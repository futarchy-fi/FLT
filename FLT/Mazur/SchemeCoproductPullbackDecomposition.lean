/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pullbacks of scheme coproducts decompose by ordered components

For arbitrary maps from two coproducts, the component fiber products form a
disjoint open cover and their coproduct is the original fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeCoproductPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {I J : Type u} (X : I → Scheme.{u}) (Y : J → Scheme.{u}) {S : Scheme.{u}}
  (f : (∐ X) ⟶ S) (g : (∐ Y) ⟶ S)

/-- The actual fiber product of one component from each source. -/
abbrev chart (ij : I × J) : Scheme.{u} :=
  pullback (Sigma.ι X ij.1 ≫ f) (Sigma.ι Y ij.2 ≫ g)

/-- The component fiber product maps into the full fiber product. -/
def chartMap (ij : I × J) : chart X Y f g ij ⟶ pullback f g :=
  pullback.map _ _ _ _ (Sigma.ι X ij.1) (Sigma.ι Y ij.2) (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)

/-- The component map retains the first projection. -/
@[reassoc] theorem chartMap_fst (ij : I × J) :
    chartMap X Y f g ij ≫ pullback.fst f g =
      pullback.fst _ _ ≫ Sigma.ι X ij.1 := pullback.lift_fst _ _ _

/-- The component map retains the second projection. -/
@[reassoc] theorem chartMap_snd (ij : I × J) :
    chartMap X Y f g ij ≫ pullback.snd f g =
      pullback.snd _ _ ≫ Sigma.ι Y ij.2 := pullback.lift_snd _ _ _

/-- Each component fiber product is an open subscheme. -/
instance chartMap_isOpenImmersion (ij : I × J) : IsOpenImmersion (chartMap X Y f g ij) := by
  unfold chartMap
  infer_instance

/-- Component fiber products cover the original fiber product. -/
def cover : (pullback f g).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover X) (sigmaOpenCover Y) f g

/-- The covering maps are exactly the actual component comparison maps. -/
theorem cover_map (ij : I × J) : (cover X Y f g).f ij = chartMap X Y f g ij := rfl

/-- Different ordered component pairs give disjoint opens. -/
theorem chartMap_disjoint :
    Pairwise (fun ij kl ↦ Disjoint (chartMap X Y f g ij).opensRange
      (chartMap X Y f g kl).opensRange) := by
  intro ij kl h V hi hj x hx
  obtain ⟨a, ha⟩ := hi hx
  obtain ⟨b, hb⟩ := hj hx
  have hf := congrArg (pullback.fst f g) (ha.trans hb.symm)
  have hs := congrArg (pullback.snd f g) (ha.trans hb.symm)
  change (chartMap X Y f g ij ≫ pullback.fst f g) a =
    (chartMap X Y f g kl ≫ pullback.fst f g) b at hf
  change (chartMap X Y f g ij ≫ pullback.snd f g) a =
    (chartMap X Y f g kl ≫ pullback.snd f g) b at hs
  rw [chartMap_fst, chartMap_fst] at hf
  rw [chartMap_snd, chartMap_snd] at hs
  have h₁ := congrArg Sigma.fst ((sigmaι_eq_iff X _ _ _ _).mp hf)
  have h₂ := congrArg Sigma.fst ((sigmaι_eq_iff Y _ _ _ _).mp hs)
  exact (h (Prod.ext h₁ h₂)).elim

/-- The coproduct of component fiber products is the actual full fiber product. -/
def decompositionIso : (∐ chart X Y f g) ≅ pullback f g := by
  have hc := nonempty_isColimit_cofanMk_of (chartMap X Y f g)
    (cover X Y f g).iSup_opensRange (chartMap_disjoint X Y f g)
  let _ : IsIso (Sigma.desc (chartMap X Y f g)) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk _ (chartMap X Y f g))).mp hc
  exact asIso (Sigma.desc (chartMap X Y f g))

/-- The decomposition retains every original component inclusion. -/
@[reassoc] theorem decompositionIso_inclusion (ij : I × J) :
    Sigma.ι (chart X Y f g) ij ≫ (decompositionIso X Y f g).hom = chartMap X Y f g ij :=
  Sigma.ι_comp_desc _ _

end FLT.Mazur.SchemeCoproductPullback
