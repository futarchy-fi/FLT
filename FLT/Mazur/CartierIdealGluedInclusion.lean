/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealInclusionDescentMap

/-!
# Descending the original full ideal inclusion

Fullness of effective line descent constructs a map from the glued line to the
structure sheaf. Its pullback is the given ideal inclusion under the original
recovery isomorphism and the canonical structure-module frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemeGeometricDescent SchemeAffineDescent SchemePicard
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{0}} (p : Y ⟶ X)
  [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

/-- The inclusion into the structure sheaf constructed by effective descent. -/
def cartierIdealGluedInclusion :
    (cartierIdealGluedLine p I hI h).val ⟶ structureModule X :=
  ((lineDescentEquivalence p).fullyFaithfulFunctor.preimage
    ((cartierIdealGluedLineRecovery p I hI h).hom ≫
      cartierIdealInclusionDescentMap p I hI h)).hom

/-- The descended inclusion recovers the actual source ideal embedding. -/
lemma cartierIdealGluedInclusion_recovery :
    (pullback p).map (cartierIdealGluedInclusion p I hI h) ≫
        (modulePullbackUnitIso p).hom =
      (cartierIdealGluedLineIso p I hI h).hom ≫ idealModuleι I := by
  have he := congrArg Subtype.val
    ((lineDescentEquivalence p).fullyFaithfulFunctor.map_preimage
      ((cartierIdealGluedLineRecovery p I hI h).hom ≫
        cartierIdealInclusionDescentMap p I hI h))
  change (pullback p).map (cartierIdealGluedInclusion p I hI h) =
    (cartierIdealGluedLineIso p I hI h).hom ≫
      idealModuleι I ≫ (modulePullbackUnitIso p).inv at he
  rw [he, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual pulled-back map is monic, before descending monicity to the base. -/
theorem cartierIdealGluedInclusion_pullback_mono :
    Mono ((pullback p).map (cartierIdealGluedInclusion p I hI h)) :=
  mono_of_mono_fac (cartierIdealGluedInclusion_recovery p I hI h)

end FLT.Mazur.FCurve
