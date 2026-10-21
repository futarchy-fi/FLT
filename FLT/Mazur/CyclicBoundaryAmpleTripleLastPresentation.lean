/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleTripleSubgroup
public import FLT.Mazur.CompatibleSubgroupPresentationAssociativity

/-!
# Original presentations for the last two stages of an ample tower

The independently constructed last-two-stages subgroup comparison is the
transport of the original three-stage presentation. The comparison retains
the actual two-stage isomorphism rather than choosing a replacement.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (g : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U)
  (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleTripleLast_separated {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [IsSeparated F.group.hom] (f : Y ⟶ X) :
    IsSeparated (F.baseChange f).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd F.group.hom f))

local instance ampleTripleLast_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (f : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange f).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom f
    inferInstance

local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel E n))
local notation "A" => Sigma.snd (Subtype.val (ampleUniversalLevel (E.baseChange g) n))
local notation "p₀" => ampleBaseChangeToOriginal g E n
local notation "p₁" => ampleBaseChangeToOriginal h (E.baseChange g) n
local notation "p₂" => ampleBaseChangeToOriginal k
  (GeneralizedEllipticCurve.baseChange (E.baseChange g) h) n
local notation "a₀" => ampleBaseChangeSubgroupIso g E n
local notation "a₁" => ampleBaseChangeSubgroupIso h (E.baseChange g) n
local notation "a₂" => ampleBaseChangeSubgroupIso k
  (GeneralizedEllipticCurve.baseChange (E.baseChange g) h) n
local notation "s" => ampleBaseChangeToOriginal (k ≫ h) (E.baseChange g) n
local notation "t" => Iso.hom (ampleBaseChangeTowerIso h k (E.baseChange g) n)

/-- Flattening the last two stages gives the original full three-stage subgroup presentation. -/
theorem ampleTriplePresentation_eq_last :
    ampleTriplePresentation g h k E n =
      (by
        have d := compatiblePresentationExtension (H) (p₀) (a₀) ((p₂) ≫ (p₁))
          (ampleBaseChangeTowerSubgroupIso h k (E.baseChange g) n)
        rw [Category.assoc] at d
        exact d) :=
  compatiblePresentationExtension_assoc (H) (p₀) (p₁) (p₂) (a₀) (a₁) (a₂)

/-- The actual last-two-stages comparison is transport between the original presentations. -/
theorem ampleTowerLastSubgroupIso_eq_transport :
    ampleTowerIsoSubgroupIso h k (E.baseChange g) n =
      compatibleRefinementTransport (H) ((s) ≫ (p₀)) ((p₂) ≫ (p₁) ≫ (p₀)) (t)
        (by rw [ampleBaseChangeTowerIso_original_assoc])
        (ampleBaseChangeTowerSubgroupIso g (k ≫ h) E n)
        (ampleTriplePresentation g h k E n) := by
  rw [ampleTowerIsoSubgroupIso_eq_transport, ampleTriplePresentation_eq_last]
  have he := compatibleRefinementTransport_extension (H) (p₀) (a₀) (s)
    ((p₂) ≫ (p₁)) (t) (ampleBaseChangeTowerIso_original h k (E.baseChange g) n).symm
    (ampleBaseChangeSubgroupIso (k ≫ h) (E.baseChange g) n)
    (ampleBaseChangeTowerSubgroupIso h k (E.baseChange g) n)
  exact he.symm.trans (compatibleRefinementTransport_source_cast (H) ((s) ≫ (p₀))
    (((p₂) ≫ (p₁)) ≫ (p₀)) ((p₂) ≫ (p₁) ≫ (p₀)) (t)
    (by rw [ampleBaseChangeTowerIso_original_assoc, Category.assoc]) (Category.assoc _ _ _).symm
    (ampleBaseChangeTowerSubgroupIso g (k ≫ h) E n)
    (compatiblePresentationExtension (H) (p₀) (a₀) ((p₂) ≫ (p₁))
      (ampleBaseChangeTowerSubgroupIso h k (E.baseChange g) n))).symm

end FLT.Mazur.CyclicBoundaryParameter
