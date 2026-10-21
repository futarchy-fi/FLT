/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryFaithfulOpen

/-!
# The faithful boundary open represents faithfulness of the cyclic projection

The factorization criterion is stated on arbitrary relative test schemes.
Auxiliary markings are retained without imposing injectivity on them.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (n : ℕ) [NeZero n]

instance cyclicFaithfulInclusion_mono : Mono (cyclicFaithfulInclusion E n) := by
  have : Mono (cyclicFaithfulInclusion E n).left :=
    inferInstanceAs (Mono (cyclicFaithfulOpen E n).ι)
  exact Over.mono_of_mono_left _

/-- Every relative test of the faithful open has a universally faithful cyclic projection. -/
theorem cyclicFaithful_projection {U : Over S} (f : U ⟶ cyclicFaithfulParameter E n) :
    AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      (f ≫ cyclicFaithfulInclusion E n ≫ cyclicProjection E n) := by
  have h := AuxiliaryLevel.faithfulInclusion_universallyFaithful E
    (Multiplicative (ZMod n)) (f ≫ cyclicFaithfulProjection E n)
  simpa only [Category.assoc, cyclicFaithfulProjection_inclusion] using h

/-- Lift the entire parameter from universal faithfulness of its actual cyclic projection. -/
def projectionFaithfulLift {U : Over S} (f : U ⟶ parameter E n)
    (hf : AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n)) : U ⟶ cyclicFaithfulParameter E n :=
  Over.homMk (IsOpenImmersion.lift (cyclicFaithfulOpen E n).ι f.left (by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨f.left x, ?_⟩, rfl⟩
    exact AuxiliaryLevel.universallyFaithful_range E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n) hf ⟨x, rfl⟩)) (by
        change _ ≫ (cyclicFaithfulOpen E n).ι ≫ (parameter E n).hom = U.hom
        rw [IsOpenImmersion.lift_fac_assoc, f.w])

/-- The lifted relative test retains every auxiliary and cyclic label. -/
@[reassoc] theorem projectionFaithfulLift_inclusion {U : Over S}
    (f : U ⟶ parameter E n)
    (hf : AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n)) :
    projectionFaithfulLift E n f hf ≫ cyclicFaithfulInclusion E n = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Cyclic projection faithfulness is represented exactly on every relative test. -/
theorem cyclicFaithful_projection_iff {U : Over S} (f : U ⟶ parameter E n) :
    AuxiliaryLevel.UniversallyFaithful E (Multiplicative (ZMod n))
      (f ≫ cyclicProjection E n) ↔
    ∃! v : U ⟶ cyclicFaithfulParameter E n, v ≫ cyclicFaithfulInclusion E n = f := by
  constructor
  · intro hf
    refine ⟨projectionFaithfulLift E n f hf, projectionFaithfulLift_inclusion E n f hf, ?_⟩
    intro v hv
    apply (cancel_mono (cyclicFaithfulInclusion E n)).mp
    exact hv.trans (projectionFaithfulLift_inclusion E n f hf).symm
  · rintro ⟨v, rfl, _⟩
    simpa only [Category.assoc] using cyclicFaithful_projection E n v

end FLT.Mazur.CyclicBoundaryParameter
