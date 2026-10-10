/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedBaseSectionNumerator
public import FLT.Mazur.StalkBaseLocalization

/-!
# Actual numerators for sections over a base local ring

Every quasi-coherent section after stalk base change is the pullback of a
global section up to multiplication by a base denominator outside the chosen
prime. That denominator is a unit on the local-ring family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsAffine S] [CompactSpace X] [X.IsSeparated]
  (f : X ⟶ S) (s : S) (M : X.Modules) [M.IsQuasicoherent]

/-- A local-ring section has a global numerator with denominator outside the point prime. -/
theorem exists_section_numerator
    (t : Γ((Scheme.Modules.pullback (toSource f s)).obj M, ⊤)) :
    ∃ (r : (pointIdeal S s).primeCompl) (a : Γ(M, ⊤)),
      pullGlobal (toSource f s) M a =
        (projection f s).appTop ((S.fromSpecStalk s).appTop r.val) • t := by
  let _ := fromSpecStalk_flat S s
  exact FlatGlobalSectionBaseChange.exists_localized_section_numerator
    (IsPullback.of_hasPullback f (S.fromSpecStalk s)) M (pointIdeal S s).primeCompl
      (fromSpecStalk_appTop_isLocalization S s) t

omit [CompactSpace X] [X.IsSeparated] in
/-- Every denominator used above is a unit on the actual local-ring family. -/
theorem denominator_isUnit (r : (pointIdeal S s).primeCompl) :
    IsUnit ((projection f s).appTop ((S.fromSpecStalk s).appTop r.val)) := by
  let _ := (S.fromSpecStalk s).appTop.hom.toAlgebra
  let _ := fromSpecStalk_appTop_isLocalization S s
  exact (IsLocalization.map_units Γ(Spec (S.presheaf.stalk s), ⊤) r).map
    (projection f s).appTop.hom

end FLT.Mazur.StalkBase
