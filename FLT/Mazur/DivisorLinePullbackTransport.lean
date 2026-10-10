/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullbackIdentity

/-!
# Transported coherence of divisor-line pullback

Functorial systems provide equality with identity and composite morphisms,
rather than definitional identity. These laws retain the actual pullback
transport along those equalities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.FCurve

variable {X Y Z : Scheme} {I : Z.IdealSheafData} {J : Y.IdealSheafData}
variable {K : X.IdealSheafData}

/-- Composition coherence includes the specified equality of the composite scheme map. -/
theorem divisorLinePullbackIsoOfEq_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : k = f ≫ g)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (hg : I.comap g = J) (hf : J.comap f = K) (hkg : I.comap k = K)
    [IsIso (idealModulePullbackHom I g)] [IsIso (idealModulePullbackHom J f)]
    [IsIso (idealModulePullbackHom I k)] :
    (pullback f).mapIso (divisorLinePullbackIsoOfEq g hI hJ hg) ≪≫
        divisorLinePullbackIsoOfEq f hJ hK hf =
      (pullbackComp f g).app (divisorLineBundle I hI) ≪≫
        (pullbackCongr hk.symm).app (divisorLineBundle I hI) ≪≫
          divisorLinePullbackIsoOfEq k hI hK hkg := by
  subst k
  apply Iso.ext
  simpa [pullbackCongr] using
    congrArg Iso.hom (divisorLinePullbackIsoOfEq_comp f g hI hJ hK hg hf hkg)

/-- Identity coherence includes the specified equality with the identity scheme map. -/
theorem divisorLinePullbackIsoOfEq_id_eq (f : X ⟶ X) (hf : f = 𝟙 X)
    (I : X.IdealSheafData) (hI : EffectiveCartier I) (hi : I.comap f = I)
    [IsIso (idealModulePullbackHom I f)] :
    divisorLinePullbackIsoOfEq f hI hI hi =
      (pullbackCongr hf).app (divisorLineBundle I hI) ≪≫
        (pullbackId X).app (divisorLineBundle I hI) := by
  subst f
  apply Iso.ext
  simpa [pullbackCongr] using congrArg Iso.hom (divisorLinePullbackIsoOfEq_id I hI)

end FLT.Mazur.FCurve
