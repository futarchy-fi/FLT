/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransportSubgroup
public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Ample boundary charts retain full curve isomorphisms

Ampleness is preserved on every scheme test by the actual subgroup comparison.
This constructs an isomorphism of ample parameter schemes, retaining their
original faithful parameters, including over singular and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  [SmoothOfRelativeDimension 1 E.group.hom] [SmoothOfRelativeDimension 1 F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]
local notation "q" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso e n))
local notation "I" => ampleParameterOpen E n
local notation "J" => ampleParameterOpen F n

/-- Full subgroup transport on every test of the original faithful parameter. -/
def faithfulTransportTestSubgroupIso {T : Scheme}
    (u : T ⟶ (cyclicFaithfulParameter E.group n).left) :
    CompatibleIso ((faithfulUniversalSubgroup E n).baseChange u)
      ((faithfulUniversalSubgroup F n).baseChange (u ≫ (q))) :=
  ((faithfulTransportSubgroupIso e n).baseChange u).trans
    ((faithfulUniversalSubgroup F n).compatibleBaseChangeComp (q) u).symm

/-- Actual curve transport preserves and reflects the ample parameter criterion. -/
theorem ampleParameter_curveTransport_criterion {T : Scheme}
    (u : T ⟶ (cyclicFaithfulParameter E.group n).left) :
    Set.range u ⊆ (I) ↔ Set.range (u ≫ (q)) ⊆ (J) :=
  ((faithfulUniversalSubgroup E n).isAmple_baseChange_iff_range
    (faithfulUniversalSubgroup_cartier E n).1 u).symm.trans
      ((faithfulTransportTestSubgroupIso e n u).isAmple_iff.trans
        ((faithfulUniversalSubgroup F n).isAmple_baseChange_iff_range
          (faithfulUniversalSubgroup_cartier F n).1 (u ≫ (q))))

/-- Restrict the full curve comparison to the actual ample chart. -/
def ampleCurveTransport : ampleParameter E n ⟶ ampleParameter F n :=
  (faithfulUniversalSubgroup F n).ampleOpenLift (faithfulUniversalSubgroup_cartier F n).1
    ((I).ι ≫ (q)) ((faithfulTransportTestSubgroupIso e n (I).ι).isAmple_iff.mp
      ((faithfulUniversalSubgroup E n).ampleOpen_isAmple
        (faithfulUniversalSubgroup_cartier E n).1))

/-- The ample transport retains the entire original faithful parameter. -/
@[reassoc] theorem ampleCurveTransport_inclusion :
    ampleCurveTransport e n ≫ (J).ι = (I).ι ≫ (q) :=
  (faithfulUniversalSubgroup F n).ampleOpenLift_inclusion _ _ _

/-- The inverse full curve comparison restores the original ample parameter. -/
theorem ampleCurveTransport_inverse :
    ampleCurveTransport e n ≫ ampleCurveTransport e.symm n = 𝟙 _ := by
  apply (cancel_mono (I).ι).mp
  rw [Category.assoc, ampleCurveTransport_inclusion, ampleCurveTransport_inclusion_assoc]
  have he : (q) ≫ (faithfulCurveTransportIso e.symm n).hom.left = 𝟙 _ :=
    congrArg Over.Hom.left (faithfulCurveTransportIso e n).hom_inv_id
  rw [he, Category.comp_id, Category.id_comp]

/-- Full curve isomorphisms induce actual isomorphisms of the ample boundary schemes. -/
def ampleCurveTransportIso : ampleParameter E n ≅ ampleParameter F n where
  hom := ampleCurveTransport e n
  inv := ampleCurveTransport e.symm n
  hom_inv_id := ampleCurveTransport_inverse e n
  inv_hom_id := ampleCurveTransport_inverse e.symm n

/-- The two ample opens correspond exactly under the faithful parameter isomorphism. -/
theorem ampleParameterOpen_curveTransport : (I) = (q) ⁻¹ᵁ (J) := by
  apply le_antisymm
  · intro x hx
    have hr := (ampleParameter_curveTransport_criterion e n (I).ι).mp (by
      rintro _ ⟨y, rfl⟩
      exact y.property)
    exact hr ⟨⟨x, hx⟩, rfl⟩
  · intro x hx
    have hr := (ampleParameter_curveTransport_criterion e n ((q) ⁻¹ᵁ (J)).ι).mpr (by
      rintro _ ⟨y, rfl⟩
      exact y.property)
    exact hr ⟨⟨x, hx⟩, rfl⟩

end FLT.Mazur.CyclicBoundaryParameter
