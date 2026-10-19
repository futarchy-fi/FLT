/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupClassification
public import FLT.Mazur.CompatibleSubgroupCartierGeneratorEquiv

/-!
# Affine closed comparison parameters with arbitrary Cartier generators

Every compatible full comparison and every target Cartier generator arise
from a unique closed comparison parameter and source Cartier generator.
The generators are allowed to vary independently of any chosen chart marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A : Type} [CommRing A]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (B : Type) [CommRing B] [Algebra A B]
local notation "t" => Spec.algebraMap A B
local notation "H" => FiniteSubgroup.baseChange (normalizedSubgroup n b) (t ≫ q)
local notation "J" => FiniteSubgroup.baseChange (normalizedSubgroup n c) (t ≫ r)

/-- Closed parameters with a source generator classify all comparisons with a target generator. -/
def affineSubgroupCartierPointEquiv :
    (Σ _k : {k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r //
      k ≫ affineSubgroupStructure n b c q r = t},
      {P : 𝟙_ (Over (Spec (.of B))) ⟶ (H).carrier // (H).IsCartierGenerator P}) ≃
    (Σ _a : CompatibleIso H J,
      {Q : 𝟙_ (Over (Spec (.of B))) ⟶ (J).carrier // (J).IsCartierGenerator Q}) :=
  Equiv.sigmaCongr (affineSubgroupPointEquiv n b c q r B)
    (fun k ↦ compatibleCartierGeneratorEquiv (affineSubgroupPointEquiv n b c q r B k))

/-- All prescribed comparison and Cartier-generator pairs have a unique actual local parameter. -/
theorem affineSubgroupCartierPointEquiv_unique (a : CompatibleIso H J)
    (Q : {Q : 𝟙_ (Over (Spec (.of B))) ⟶ (J).carrier // (J).IsCartierGenerator Q}) :
    ∃! z : Σ _k : {k : Spec (.of B) ⟶ affineSubgroupScheme n b c q r //
      k ≫ affineSubgroupStructure n b c q r = t},
      {P : 𝟙_ (Over (Spec (.of B))) ⟶ (H).carrier // (H).IsCartierGenerator P},
      affineSubgroupCartierPointEquiv n b c q r B z = ⟨a, Q⟩ :=
  (affineSubgroupCartierPointEquiv n b c q r B).bijective.existsUnique ⟨a, Q⟩

end FLT.Mazur.CyclicCharacteristicAtlas
