/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedRecoveryCompatibility

/-!
# Canonical effective pair maps preserve the transferred rigidifications

Pull the original recovery square to the original pair section and use
preservation by the original transition and both original recovery maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


/-- The actual canonical effective pair preserves the transferred local rigidifications. -/
theorem rigidifiedFamilyEffectivePair_preserves (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback (pointedBaseSection f e he (relativeCoverPair T 𝒰 i j))).map
        (rigidifiedFamilyEffectivePair f e he T 𝒰 a ha i j).hom ≫
      (rigidifiedBasePullback f e he (relativeCoverPairRight T 𝒰 i j)
        (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha j)).2.hom =
      (rigidifiedBasePullback f e he (relativeCoverPairLeft T 𝒰 i j)
        (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i)).2.hom := by
  have hi := (rigidifiedBaseIsoPullback f e he (relativeCoverPairLeft T 𝒰 i j)
    (rigidifiedFamilyRestrictedIso f e he T 𝒰 a ha i)).property
  have hj := (rigidifiedBaseIsoPullback f e he (relativeCoverPairRight T 𝒰 i j)
    (rigidifiedFamilyRestrictedIso f e he T 𝒰 a ha j)).property
  have ht := (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).property
  have h := congrArg (fun m ↦
    (Scheme.Modules.pullback (pointedBaseSection f e he (relativeCoverPair T 𝒰 i j))).map
      m ≫ (rigidifiedBasePullback f e he (relativeCoverPairRight T 𝒰 i j)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a j)).2.hom)
    (rigidifiedFamilyDescendedMember_pair f e he T 𝒰 a ha i j)
  dsimp only [rigidifiedBaseIsoPullback, rigidifiedIsoPullback,
    rigidifiedFamilyRestrictedIso, Functor.mapIso_hom] at hi hj
  simpa only [Functor.map_comp, Category.assoc, hj, ht, hi] using h

/-- The canonical pair carries its proved preservation, without replacing its underlying map. -/
def rigidifiedFamilyEffectivePairIso (i j : 𝒰.I₀) :
    RigidifiedIso (pointedBaseSection f e he (relativeCoverPair T 𝒰 i j))
      (rigidifiedBasePullback f e he (relativeCoverPairLeft T 𝒰 i j)
        (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i)).2
      (rigidifiedBasePullback f e he (relativeCoverPairRight T 𝒰 i j)
        (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha j)).2 :=
  ⟨rigidifiedFamilyEffectivePair f e he T 𝒰 a ha i j,
    rigidifiedFamilyEffectivePair_preserves f e he T 𝒰 a ha i j⟩

end FLT.Mazur.SchemePicard
