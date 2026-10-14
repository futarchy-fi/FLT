/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationJointModelGeometry
public import FLT.Mazur.SchemeEtaleImageDenseModel

/-!
# Joint finite coefficients on an etale full-kernel source

The inclusion of joint coefficients proves schematic dominance without any
reducedness hypothesis. An etale full-kernel map to an old separated model
therefore constructs an etale joint projection and an actual scheme comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationJointModel
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {E A : Scheme} (p q : E ⟶ A)
  {C D : Type} [CommRing C] [CommRing D]
  (c : C →+* compatibleFunctions p q) (d : D →+* compatibleFunctions p q)
local notation "j" => projection p q c d

/-- The coefficient inclusion detects nilpotents as well as ordinary source functions. -/
instance projection_schematicallyDominant : IsSchemeTheoreticallyDominant (projection p q c d) := by
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  change (projection p q c d).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥
  apply le_bot_iff.mp
  refine ((projection p q c d).ideal_ker_le _).trans ?_
  change RingHom.ker (projection p q c d).appTop.hom ≤ ⊥
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (projection_appTop_injective p q c d)]

variable [IsAffine A] {T : Scheme} (w : A ⟶ T) [Etale w]
  (H : IsPullback p q w w) (r : target p q c d ⟶ T)
  [IsSeparated r] (hr : projection p q c d ≫ r = w)
local instance jointProjection_quasiCompact : QuasiCompact (projection p q c d) := by
  infer_instance

include H hr in
/-- Joint finite coefficients inherit etaleness on the complete selected source. -/
theorem projection_etale_of_kernel : Etale (projection p q c d) :=
  SchemeEtaleImageDenseModel.projection_etale w H j (projection_condition p q c d) r hr

/-- The original quotient open has a constructed scheme comparison into the joint model. -/
def etaleImageComparison : (SchemeEtaleImageQuotient.image w).toScheme ⟶ target p q c d :=
  SchemeEtaleImageDenseModel.comparison w H j (projection_condition p q c d)

include hr in
/-- The image comparison is open, preserving the complete scheme structure. -/
theorem etaleImageComparison_isOpenImmersion :
    IsOpenImmersion (etaleImageComparison p q c d w H) :=
  SchemeEtaleImageDenseModel.comparison_isOpenImmersion w H j (projection_condition p q c d) r hr

omit [IsAffine A] in
/-- The old coefficient-image quotient recovers the entire original joint projection. -/
@[reassoc]
theorem etaleImageComparison_source : SchemeEtaleImageQuotient.projection w ≫
    etaleImageComparison p q c d w H = j :=
  SchemeEtaleImageDenseModel.projection_comparison w H j (projection_condition p q c d)

omit [IsAffine A] in
/-- Both independent coefficient systems survive the actual descended scheme map. -/
theorem etaleImageComparison_coefficients :
    SchemeEtaleImageQuotient.projection w ≫ etaleImageComparison p q c d w H ≫
      toLeft p q c d = coefficientProjection p q c ∧
    SchemeEtaleImageQuotient.projection w ≫ etaleImageComparison p q c d w H ≫
      toRight p q c d = coefficientProjection p q d := by
  constructor
  · rw [etaleImageComparison_source_assoc, projection_toLeft]
  · rw [etaleImageComparison_source_assoc, projection_toRight]

/-- The old quotient is the actual joint fppf region, not just a pointwise bijection. -/
def etaleImageEffectiveIso [LocallyOfFinitePresentation (projection p q c d)] :
    (SchemeEtaleImageQuotient.image w).toScheme ≅ (SchemeFppfTargetOpen.locus j).toScheme :=
  SchemeEtaleImageDenseModel.effectiveIso w H j (projection_condition p q c d) r hr

end FLT.Mazur.SchemeRelationJointModel
