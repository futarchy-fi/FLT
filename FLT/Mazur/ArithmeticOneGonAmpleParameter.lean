/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonChangedSubgroupAmple
public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.WeierstrassSmoothOpenRelativeDimension

/-!
# The whole faithful cyclic parameter of the arithmetic one-gon is ample

The actual arithmetic cubic has integral geometric fibers, so every faithful
positive-rank cyclic subgroup is ample. Thus restricting to the ample open
loses no parameter, over an arbitrary coefficient ring, including mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup
open OneGonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))

instance arithmeticBoundaryGroup_separated : IsSeparated (curve t ht).group.hom :=
  relativeGroup_separated t

instance arithmeticBoundaryGroup_relativeDimension :
    SmoothOfRelativeDimension 1 (curve t ht).group.hom :=
  integralSmoothStructure_relativeDimension (equation t)

variable (n : ℕ) [NeZero n]
local notation "E" => curve t ht
local notation "B" => cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E)) n
local notation "H" => faithfulUniversalSubgroup (E) n
local notation "I" => ampleParameterOpen (E) n

/-- The actual universal subgroup is ample on the entire arithmetic faithful parameter scheme. -/
theorem faithfulUniversalSubgroup_isAmple : (H).IsAmple :=
  ArithmeticOneGonSubgroupAmple.isAmple_after_baseChange t ht (B).hom (H)
    (NeZero.pos n) (faithfulUniversalSubgroup_cartier (E) n).1

/-- The ample locus is the whole arithmetic faithful parameter, with no field hypothesis. -/
theorem ampleParameterOpen_eq_top : (I) = ⊤ := by
  apply top_unique
  intro x _
  exact ((H).isAmple_baseChange_iff_range
    (faithfulUniversalSubgroup_cartier (E) n).1 (𝟙 (B).left)).mp
      ((faithfulUniversalSubgroup_isAmple t ht n).baseChange (𝟙 (B).left)) ⟨x, rfl⟩

/-- Every arithmetic faithful parameter factors through the actual ample chart. -/
def faithfulToAmple : (B).left ⟶ ampleParameter (E) n :=
  (H).ampleOpenLift (faithfulUniversalSubgroup_cartier (E) n).1 (𝟙 _)
    ((faithfulUniversalSubgroup_isAmple t ht n).baseChange (𝟙 _))

/-- The factorization retains the original arithmetic parameter exactly. -/
@[reassoc] theorem faithfulToAmple_inclusion : faithfulToAmple t ht n ≫ (I).ι = 𝟙 _ :=
  (H).ampleOpenLift_inclusion _ _ _

/-- The faithful and ample arithmetic charts are canonically the same actual scheme. -/
def faithfulAmpleIso : (B).left ≅ ampleParameter (E) n where
  hom := faithfulToAmple t ht n
  inv := (I).ι
  hom_inv_id := faithfulToAmple_inclusion t ht n
  inv_hom_id := by
    apply (cancel_mono (I).ι).mp
    rw [Category.assoc, faithfulToAmple_inclusion, Category.comp_id, Category.id_comp]

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
