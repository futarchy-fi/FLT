/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Changing the presentation of a closed pullback

An isomorphism over the ambient scheme identifies the two pushforwards of
actual pullbacks. The comparison carries the pullback adjunction unit to the
original unit, so it preserves reduction maps on sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.IsomorphicClosedPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Z Y : Scheme} (e : X ≅ Z) (i : Z ⟶ Y) (L : Y.Modules)

/-- Isomorphic changes of source make the actual pullback adjunction unit invertible. -/
instance iso_unit_isIso (M : Z.Modules) :
    IsIso ((pullbackPushforwardAdjunction e.hom).unit.app M) := by
  let _ : (pullback e.hom).Full :=
    inferInstanceAs (AffineModuleGlobalSections.pullbackEquivalence e).functor.Full
  let _ : (pullback e.hom).Faithful :=
    inferInstanceAs (AffineModuleGlobalSections.pullbackEquivalence e).functor.Faithful
  infer_instance

/-- An isomorphic source presentation preserves the pushed-forward actual pullback. -/
def compositeIso : (pushforward i).obj ((pullback i).obj L) ≅
    (pushforward (e.hom ≫ i)).obj ((pullback (e.hom ≫ i)).obj L) :=
  (pushforward i).mapIso
    (asIso ((pullbackPushforwardAdjunction e.hom).unit.app ((pullback i).obj L))) ≪≫
  (pushforwardComp e.hom i).app _ ≪≫
  (pushforward (e.hom ≫ i)).mapIso ((pullbackComp e.hom i).app L)

/-- The comparison preserves the canonical projection to the pullback. -/
@[reassoc] theorem unit_compositeIso :
    (pullbackPushforwardAdjunction i).unit.app L ≫ (compositeIso e i L).hom =
      (pullbackPushforwardAdjunction (e.hom ≫ i)).unit.app L := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change ((pullbackComp e.hom i).hom.app L).app _
    (((pullbackPushforwardAdjunction e.hom).unit.app ((pullback i).obj L)).app _
      (((pullbackPushforwardAdjunction i).unit.app L).app U s)) = _
  rw [← FCurve.modulePullbackComp_inv_unit]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.app ((e.hom ≫ i) ⁻¹ᵁ U)) ((pullbackComp e.hom i).app L).inv_hom_id) _

/-- The same comparison retains a specified equality with the actual ambient morphism. -/
def overIso (f : X ⟶ Y) (h : e.hom ≫ i = f) :
    (pushforward i).obj ((pullback i).obj L) ≅ (pushforward f).obj ((pullback f).obj L) :=
  compositeIso e i L ≪≫
    eqToIso (congrArg (fun g ↦ (pushforward g).obj ((pullback g).obj L)) h)

/-- Changing the source presentation retains the original restriction to the closed source. -/
@[reassoc] theorem unit_overIso (f : X ⟶ Y) (h : e.hom ≫ i = f) :
    (pullbackPushforwardAdjunction i).unit.app L ≫ (overIso e i L f h).hom =
      (pullbackPushforwardAdjunction f).unit.app L := by
  subst f
  simpa only [overIso, eqToIso_refl, Iso.trans_refl] using unit_compositeIso e i L

end FLT.Mazur.IsomorphicClosedPullback
