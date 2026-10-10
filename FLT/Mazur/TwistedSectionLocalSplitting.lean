/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageOpenBaseChange
public import FLT.Mazur.TwistedSectionBaseChangeRegularity
public import FLT.Mazur.LocallySplitOpenCover

/-!
# Local splitting of the original twisted section on base charts

The actual transported section map is locally split exactly when the
geometric pullback of the original map is, whenever the mate is invertible.
Open base change supplies that invertibility without additional assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.TwistedSectionBaseChangeRegularity
open FCurve ModuleSheafTensor DirectImageBaseChange SplitLineAffineNeighborhood
attribute [local irreducible] tensor twistedSectionPushforwardEquiv moduleSheafDualPullbackIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) {B : S.Modules} (hB : LocallyFreeRankOne B)

/-- Invertible square comparisons preserve and reflect actual local splitting. -/
lemma section_locallySplit_iff [IsIso (comparison p q f g w L)]
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    LocallySplit (twistedSectionPushforwardEquiv q ((pullback p).obj L) (hB.pullback g)
      (section_ p q f g w L s)) ↔
      LocallySplit ((pullback g).map (twistedSectionPushforwardEquiv f L hB s)) := by
  rw [section_map p q f g w L hB s]
  let a := moduleSheafDualPullbackIso g hB
  let b := asIso (comparison p q f g w L)
  constructor
  · intro hs
    have ht := (hs.postcompose _ b.symm).precompose _ a
    simpa only [a, b, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc] using ht
  · intro hs
    exact (hs.postcompose _ b).precompose _ a.symm

/-- Splitting of the transported chart section detects splitting of the original pulled map. -/
lemma section_open_locallySplit_iff (U : S.Opens)
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    LocallySplit (twistedSectionPushforwardEquiv (f ∣_ U)
      ((pullback (f ⁻¹ᵁ U).ι).obj L) (hB.pullback U.ι)
      (section_ (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι (morphismRestrict_ι f U) L s)) ↔
      LocallySplit ((pullback U.ι).map (twistedSectionPushforwardEquiv f L hB s)) := by
  let _ := openComparison_isIso f U L
  exact section_locallySplit_iff (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι
    (morphismRestrict_ι f U) L hB s

end FLT.Mazur.TwistedSectionBaseChangeRegularity
