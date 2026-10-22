/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCanonicalLine
public import FLT.Mazur.SectionPoleAdaptedBasis

/-!
# Normalized pole lifts on original singular generalized families

Starting with the actual canonical section, prescribed leading-line frames
construct normalized lifts and bases compatible with the original inclusions.
The vanishing now holds across singular and reducible fibers of the original family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

/-- Properness is supplied by the original generalized family. -/
local instance markingPoleProper : IsProper E.curve.hom := E.family.family.1

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The degree-one tensor-power basis comes from the actual canonical divisor section. -/
def smoothMarkingOneBasis : Basis Unit Γ(S, ⊤)
    (ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) 1) 0) :=
  (smoothMarkingCanonicalBasis E s).map
    (((moduleRingHFunctor E.curve.hom.appTop.hom 0).mapIso
      (rightUnitor (divisorLineBundle (t).left.ker (hI))).symm).toLinearEquiv)

/-- The degree-one tensor unitor recovers the original canonical section. -/
theorem smoothMarkingOneBasis_section :
    (rightUnitor (divisorLineBundle (t).left.ker (hI))).hom.app ⊤
      (moduleH0Equiv _ (smoothMarkingOneBasis E s ())) = divisorSection (hI) ⊤ := by
  rw [smoothMarkingOneBasis, Basis.map_apply]
  change (rightUnitor _).hom.app ⊤
    (moduleH0Equiv _ (moduleHMap (rightUnitor _).inv 0
      (smoothMarkingCanonicalBasis E s ()))) = _
  rw [moduleH0Equiv_naturality]
  have he := ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤)
    (rightUnitor (divisorLineBundle (t).left.ker (hI))).inv_hom_id)
  exact (he _).trans (smoothMarkingCanonicalBasis_apply E s)

/-- Every positive pole degree has an actual lift with the prescribed unit leading term. -/
def smoothMarkingNormalizedLift (m : ℕ) (hm : 0 < m)
    (e : Γ(sectionPoleLine (t).left (hI) (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 1)) 0 := by
  letI : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) m) 1) :=
    smoothMarkingPower_relative_acyclic E s m hm 0
  exact sectionPoleNormalizedLift E.curve.hom (t).left (t).w (hI) m e

/-- The constructed lift has leading coefficient exactly one in the actual line frame. -/
theorem smoothMarkingNormalizedLift_leading (m : ℕ) (hm : 0 < m)
    (e : Γ(sectionPoleLine (t).left (hI) (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    e (sectionPoleLeading E.curve.hom (t).left (t).w (hI) m
      (smoothMarkingNormalizedLift E s m hm e)) = 1 := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) m) 1) :=
    smoothMarkingPower_relative_acyclic E s m hm 0
  exact sectionPoleNormalizedLift_leading E.curve.hom (t).left (t).w (hI) m e

/-- The canonical section and a normalized order-two lift form a basis. -/
def smoothMarkingTwoBasis
    (e : Γ(sectionPoleLine (t).left (hI) 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    Basis (Unit ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) 2) 0) := by
  letI : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 1) 1) :=
    smoothMarkingPower_relative_acyclic E s 1 Nat.zero_lt_one 0
  exact sectionPoleNormalizedBasis E.curve.hom (t).left (t).w (hI) 1
    (smoothMarkingOneBasis E s) e

/-- The order-three basis extends the original order-two basis by a normalized lift. -/
def smoothMarkingThreeBasis
    (e₂ : Γ(sectionPoleLine (t).left (hI) 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine (t).left (hI) 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(S, ⊤)
      (ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) 3) 0) := by
  letI : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 2) 1) :=
    smoothMarkingPower_relative_acyclic E s 2 (Nat.zero_lt_succ 1) 0
  exact sectionPoleNormalizedBasis E.curve.hom (t).left (t).w (hI) 2
    (smoothMarkingTwoBasis E s e₂) e₃

/-- The new vector at order two is the actual chosen normalized lift. -/
theorem smoothMarkingTwoBasis_new
    (e : Γ(sectionPoleLine (t).left (hI) 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    smoothMarkingTwoBasis E s e (Sum.inr ()) =
      smoothMarkingNormalizedLift E s 1 Nat.zero_lt_one e := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 1) 1) :=
    smoothMarkingPower_relative_acyclic E s 1 Nat.zero_lt_one 0
  exact sectionPoleNormalizedBasis_new E.curve.hom (t).left (t).w (hI) 1 _ e

/-- Every order-two vector enters order three by the original divisor transition. -/
theorem smoothMarkingThreeBasis_old
    (e₂ : Γ(sectionPoleLine (t).left (hI) 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine (t).left (hI) 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) (i : Unit ⊕ Unit) :
    smoothMarkingThreeBasis E s e₂ e₃ (Sum.inl i) =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) 2 (smoothMarkingTwoBasis E s e₂ i) := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 2) 1) :=
    smoothMarkingPower_relative_acyclic E s 2 (Nat.zero_lt_succ 1) 0
  exact sectionPoleAdaptedBasis_old E.curve.hom (t).left (t).w (hI) 2 _ _ i

/-- The new order-three vector is the actual normalized order-three lift. -/
theorem smoothMarkingThreeBasis_new
    (e₂ : Γ(sectionPoleLine (t).left (hI) 2, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (e₃ : Γ(sectionPoleLine (t).left (hI) 3, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    smoothMarkingThreeBasis E s e₂ e₃ (Sum.inr ()) =
      smoothMarkingNormalizedLift E s 2 (Nat.zero_lt_succ 1) e₃ := by
  let _ : Subsingleton
      (ModuleH (tensorPower (divisorLineBundle (t).left.ker (hI)) 2) 1) :=
    smoothMarkingPower_relative_acyclic E s 2 (Nat.zero_lt_succ 1) 0
  exact sectionPoleNormalizedBasis_new E.curve.hom (t).left (t).w (hI) 2 _ e₃

end FLT.Mazur.GeneralizedEllipticCurve
