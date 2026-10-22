/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveRelativeMarkingFrames
public import FLT.Mazur.RelativeGenusOneCanonicalBasis

/-!
# The original canonical pole section across singular fibers

The degree-one pole direct image is a line. The actual relative Cartier
section trivializes this line, providing the canonical starting vector for
pole coordinates on the original singular family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve CartierAbel ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionNeutralTwistIso twistedSectionPushforwardEquiv
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)

/-- The actual point-line direct image has rank one across every singular fiber. -/
theorem smoothMarkingLine_pushforward_rankOne :
    LocallyFreeRankOne ((pushforward E.curve.hom).obj (L)) := by
  have h : LocallyFreeRankOne
      ((pushforward E.curve.hom).obj (E.smoothMarkingPower s 1)) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := E.smoothMarkingPower_frame s 1 Nat.zero_lt_one x
    exact ⟨U, hx, ⟨e ≪≫ Limits.coproductUniqueIso
      (fun _ : Fin 1 ↦ structureModule U.toScheme)⟩⟩
  exact h.of_iso ((pushforward E.curve.hom).mapIso (rightUnitor (L)))

/-- The original canonical section is an invertible map onto its point-line direct image. -/
theorem smoothMarking_canonicalSectionMap_isIso :
    IsIso (sectionDirectImageMap E.curve.hom (L) (divisorSection (hI) ⊤)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Surjective E.curve.hom := ⟨fun x ↦ ⟨(t).left x,
    congrArg (fun f : S ⟶ S ↦ f x) (t).w⟩⟩
  have hn := E.smoothMarkingLine_pushforward_rankOne s
  let a := sectionDivisorRelativeSection E.curve.hom (t).left (t).w (hI)
  have hi := (relativeSection_directImage_locallySplit E.curve.hom (L)
    (hI).divisorLineBundle_locallyFreeRankOne hn.locallyFiniteFree a).isIso _
      structureModule_locallyFreeRankOne.dual hn
  have he := neutralTwist_directImage E.curve.hom (L) (divisorSection (hI) ⊤)
  change IsIso (twistedSectionPushforwardEquiv E.curve.hom (L)
    structureModule_locallyFreeRankOne
    ((sectionNeutralTwistIso E.curve.hom (L)).inv.app ⊤ (divisorSection (hI) ⊤))) at hi
  rw [he] at hi
  exact IsIso.of_isIso_comp_left moduleSheafDualUnitIso.hom _

/-- Canonical trivialization of the actual degree-one direct image. -/
def smoothMarkingCanonicalIso :
    structureModule S ≅ (pushforward E.curve.hom).obj (L) := by
  let _ := E.smoothMarking_canonicalSectionMap_isIso s
  exact asIso (sectionDirectImageMap E.curve.hom (L) (divisorSection (hI) ⊤))

/-- The coefficient is linear over the original base ring. -/
def smoothMarkingCanonicalCoefficient :
    ModuleRingH E.curve.hom.appTop.hom (L) 0 ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤) :=
  (ringHZeroPushforwardSections E.curve.hom (L)).trans
    (((AffineModuleGlobalSections.sections S).mapIso
      (E.smoothMarkingCanonicalIso s).symm).toLinearEquiv)

/-- The normalized coefficient one gives precisely the original divisor section. -/
theorem smoothMarkingCanonicalCoefficient_symm_one :
    ringHZeroPushforwardSections E.curve.hom (L)
      ((E.smoothMarkingCanonicalCoefficient s).symm 1) = divisorSection (hI) ⊤ := by
  change ringHZeroPushforwardSections E.curve.hom (L)
    ((ringHZeroPushforwardSections E.curve.hom (L)).symm
      ((E.smoothMarkingCanonicalIso s).hom.app ⊤ (1 : Γ(S, ⊤)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact sectionDirectImageMap_one E.curve.hom (L) _

/-- The unique basis vector in degree one is normalized by the actual canonical section. -/
def smoothMarkingCanonicalBasis :
    Basis Unit Γ(S, ⊤) (ModuleRingH E.curve.hom.appTop.hom (L) 0) :=
  (Basis.singleton Unit Γ(S, ⊤)).map (E.smoothMarkingCanonicalCoefficient s).symm

/-- The canonical basis retains the original divisor section. -/
theorem smoothMarkingCanonicalBasis_apply :
    ringHZeroPushforwardSections E.curve.hom (L) (E.smoothMarkingCanonicalBasis s ()) =
      divisorSection (hI) ⊤ := by
  rw [smoothMarkingCanonicalBasis, Basis.map_apply, Basis.singleton_apply]
  exact E.smoothMarkingCanonicalCoefficient_symm_one s

end FLT.Mazur.GeneralizedEllipticCurve
