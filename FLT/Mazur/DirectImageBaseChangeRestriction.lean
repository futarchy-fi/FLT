/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangePasting
public import FLT.Mazur.DirectImageOpenBaseChange
public import FLT.Mazur.ModuleSheafPullbackIsoDetection

/-!
# Restriction and local detection of the actual base-change mate

Restriction of the original mate is its comparison over the smaller base,
conjugated by the canonical open and composition isomorphisms. Consequently
invertibility of the smaller-base mates on an open cover implies invertibility
of the single original map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.DirectImageBaseChange
open SchemePullbackSquare
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (M : X.Modules)

/-- Restriction retains the original mate and both canonical pullback comparisons. -/
@[reassoc]
lemma comparison_restrict (U : T.Opens) :
    (pullback U.ι).map (comparison p q f g w M) ≫
        (openIso q U ((pullback p).obj M)).hom ≫
          (pushforward (q ∣_ U)).map ((pullbackComp (q ⁻¹ᵁ U).ι p).hom.app M) =
      (pullbackComp U.ι g).hom.app ((pushforward f).obj M) ≫
        comparison ((q ⁻¹ᵁ U).ι ≫ p) (q ∣_ U) f (U.ι ≫ g)
          (paste_eq p q f g w _ _ _ (morphismRestrict_ι q U)) M := by
  rw [openIso_eq_comparison]
  exact comparison_paste p q f g w _ _ _ (morphismRestrict_ι q U) M

/-- Invertibility on a base open is exactly invertibility of the smaller-base mate. -/
lemma comparison_restrict_isIso_iff (U : T.Opens) :
    IsIso ((pullback U.ι).map (comparison p q f g w M)) ↔
      IsIso (comparison ((q ⁻¹ᵁ U).ι ≫ p) (q ∣_ U) f (U.ι ≫ g)
        (paste_eq p q f g w _ _ _ (morphismRestrict_ι q U)) M) := by
  have hh := congrArg IsIso (comparison_restrict p q f g w M U)
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using Iff.of_eq hh

/-- Smaller-base comparisons on a covering family detect the original mate's invertibility. -/
lemma comparison_isIso_of_openCover {ι : Type v} (U : ι → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i)
    (hM : ∀ i, IsIso (comparison ((q ⁻¹ᵁ U i).ι ≫ p) (q ∣_ U i) f ((U i).ι ≫ g)
      (paste_eq p q f g w _ _ _ (morphismRestrict_ι q (U i))) M)) :
    IsIso (comparison p q f g w M) := by
  apply ModuleSheafPullbackIsoDetection.isIso_of_openImmersionPullbacks
    _ (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι)
  · intro x
    obtain ⟨i, hi⟩ := hU x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩
  · intro i
    exact (comparison_restrict_isIso_iff p q f g w M (U i)).mpr (hM i)

end FLT.Mazur.DirectImageBaseChange
