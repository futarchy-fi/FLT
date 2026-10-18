/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryMarkingPowerProper
public import FLT.Mazur.AuxiliaryLevelFaithfulOpen
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite type of the full marking loci

For a proper group scheme the multiplication equations form a closed subscheme
of its finite power, hence a proper scheme over the base. Over a Noetherian base
the faithful open is quasi-compact as well as locally of finite type.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : Over S) [GrpObj E] [IsProper E.hom]
  (A : Type) [Group A] [Fintype A]

/-- The marking relations cut out a closed subscheme of the actual power. -/
instance homInclusion_isClosedImmersion : IsClosedImmersion (homInclusion E A).left := by
  let _ : IsSeparated (∏ᶜ fun _ : A × A => E).hom := inferInstance
  exact isClosedImmersion_equalizer_ι_left (productValues E A) (productIndices E A)

/-- The complete homomorphism parameter scheme is proper over the coefficient base. -/
instance homScheme_isProper : IsProper (homScheme E A).hom := by
  rw [← (homInclusion E A).w]
  infer_instance

/-- The faithful parameter inclusion is the actual open immersion. -/
instance faithfulInclusion_isOpenImmersion :
    IsOpenImmersion (faithfulInclusion E A).left := by
  change IsOpenImmersion (faithfulOpen E A).ι
  infer_instance

/-- Faithful marking parameters are locally of finite type over the base. -/
instance faithfulScheme_locallyOfFiniteType : LocallyOfFiniteType (faithfulScheme E A).hom := by
  rw [← (faithfulInclusion E A).w]
  infer_instance

/-- Proper homomorphism parameters over a Noetherian base are Noetherian. -/
instance homScheme_isNoetherian [IsNoetherian S] : IsNoetherian (homScheme E A).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (homScheme E A).hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (homScheme E A).hom

/-- Every faithful-marking open is quasi-compact over a Noetherian base. -/
instance faithfulScheme_quasiCompact [IsNoetherian S] :
    QuasiCompact (faithfulScheme E A).hom := by
  let _ : NoetherianSpace (faithfulScheme E A).left :=
    Topology.IsEmbedding.subtypeVal.isInducing.noetherianSpace
  infer_instance

/-- The full faithful parameter scheme is itself Noetherian. -/
instance faithfulScheme_isNoetherian [IsNoetherian S] :
    IsNoetherian (faithfulScheme E A).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (faithfulScheme E A).hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (faithfulScheme E A).hom

end FLT.Mazur.AuxiliaryLevel
