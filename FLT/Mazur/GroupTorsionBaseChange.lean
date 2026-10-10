/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionScheme
public import FLT.Mazur.GroupMarkingBaseChange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# The original torsion equalizer commutes with arbitrary base change

The monoidal pullback preserves powers, and its right adjunction preserves
the full equalizer. The resulting scheme comparison retains the original
torsion inclusion, without a flatness or reducedness hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GroupTorsionScheme

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Changing the names of equal parallel maps retains their original equalizer. -/
def equationCongr {S : Scheme} {X Y : Over S} {f g f' g' : X ⟶ Y}
    (hf : f = f') (hg : g = g') : equalizer f g ≅ equalizer f' g' :=
  eqToIso (by rw [hf, hg])

/-- The equality comparison retains the equalizer inclusion. -/
@[reassoc] theorem equationCongr_inclusion {S : Scheme} {X Y : Over S}
    {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    (equationCongr hf hg).hom ≫ equalizer.ι f' g' = equalizer.ι f g := by
  subst f'
  subst g'
  exact Category.id_comp _

variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] (n : ℕ)

local notation "F" => Over.pullback g

/-- The actual monoidal pullback carries the original power operation to the new one. -/
theorem pullback_powerMap : (F).map (powerMap E n) = powerMap ((F).obj E) n := by
  change (F).homMonoidHom ((𝟙 E) ^ n) = (𝟙 ((F).obj E)) ^ n
  rw [map_pow]
  exact congrArg (fun k => k ^ n) ((F).map_id E)

/-- The full torsion equalizer commutes with arbitrary scheme base change. -/
def baseChangeIso : (F).obj (scheme E n) ≅ scheme ((F).obj E) n :=
  PreservesEqualizer.iso F (powerMap E n) 1 ≪≫
    equationCongr (pullback_powerMap g E n) ((F).map_one)

/-- The comparison preserves the actual inclusion into the base-changed group. -/
@[reassoc] theorem baseChangeIso_inclusion :
    (baseChangeIso g E n).hom ≫ inclusion ((F).obj E) n = (F).map (inclusion E n) := by
  change ((PreservesEqualizer.iso F (powerMap E n) 1).hom ≫
    (equationCongr (pullback_powerMap g E n) (F).map_one).hom) ≫
      equalizer.ι _ _ = _
  rw [Category.assoc, equationCongr_inclusion]
  exact equalizerComparison_comp_π _ _ _

end FLT.Mazur.GroupTorsionScheme
