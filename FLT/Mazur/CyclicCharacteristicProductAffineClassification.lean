/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupClassification
public import FLT.Mazur.CyclicCharacteristicProductChartTests

/-!
# Full subgroup classification on affine tests of the glued scheme

On every affine open of the normalized product, the glued scheme classifies
all compatible subgroup comparisons of the original normalized families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
  (U : (normalizedProduct n b c).affineOpens)
local notation "K" => DirectedAffineSpectrum.Ring (normalizedProduct n b c) U
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
variable (B : Type) [CommRing B]
  [Algebra (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B]
local notation "t" => Spec.algebraMap K B

/-- Changing from spectrum coordinates to the actual affine open retains every test map. -/
def productSubgroupChartCoordinateEquiv :
    {k : Spec (.of B) ⟶ affineSubgroupScheme n b c L R //
      k ≫ affineSubgroupStructure n b c L R = t} ≃
    {k : Spec (.of B) ⟶ productOpenSubgroup n b c U //
      k ≫ productOpenSubgroupStructure n b c U = t ≫ U.1.toScheme.isoSpec.inv} :=
  Equiv.subtypeEquivRight fun k ↦ by
    change k ≫ affineSubgroupStructure n b c L R = t ↔
      k ≫ (affineSubgroupStructure n b c L R ≫ U.1.toScheme.isoSpec.inv) = _
    rw [← Category.assoc, cancel_mono]

/-- Affine tests of the glued scheme classify all original compatible subgroup isomorphisms. -/
def productSubgroupAffinePointEquiv :
    {k : Spec (.of B) ⟶ productSubgroupScheme n b c //
      k ≫ productSubgroupStructure n b c =
        (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} ≃
    CompatibleIso ((normalizedSubgroup n b).baseChange (t ≫ L))
      ((normalizedSubgroup n c).baseChange (t ≫ R)) :=
  ((productSubgroupChartCoordinateEquiv n b c U B).trans
    (productSubgroupChartTestEquiv n b c U (t ≫ U.1.toScheme.isoSpec.inv))).symm.trans
      (affineSubgroupPointEquiv (A := K) n b c L R B)

/-- Every compatible comparison has a unique actual morphism into the glued subgroup scheme. -/
theorem productSubgroupAffinePointEquiv_unique
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange (t ≫ L))
      ((normalizedSubgroup n c).baseChange (t ≫ R))) :
    ∃! k : {k : Spec (.of B) ⟶ productSubgroupScheme n b c //
      k ≫ productSubgroupStructure n b c =
        (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productSubgroupAffinePointEquiv n b c U B k = a :=
  (productSubgroupAffinePointEquiv n b c U B).bijective.existsUnique a

end FLT.Mazur.CyclicCharacteristicAtlas
