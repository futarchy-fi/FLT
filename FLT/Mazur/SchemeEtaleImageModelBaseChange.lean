/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEtaleImageDenseModel

/-!
# Complete source pullbacks over the actual quotient comparison

Every test of the old quotient, including a nonreduced change of ground base,
has the complete pulled-back joint source as a surjective etale cover.
All original coefficient maps survive as scheme morphisms on that entire source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeEtaleImageDenseModel
set_option backward.isDefEq.respectTransparency false
variable {E A T J : Scheme} {p q : E ⟶ A} (w : A ⟶ T) [Etale w]
  (H : IsPullback p q w w) (j : A ⟶ J) (hj : p ≫ j = q ≫ j)
local notation "U" => SchemeEtaleImageQuotient.image w
local notation "e" => SchemeEtaleImageQuotient.projection w
local notation "s" => comparison w H j hj

variable {Z : Scheme} (b : Z ⟶ (SchemeEtaleImageQuotient.image w).toScheme)

/-- The full original source pulled back by the actual descended joint coefficient map. -/
def completeSource : Scheme := pullback j (b ≫ s)

/-- The unchanged original source coordinate. -/
def completeToSource : completeSource w H j hj b ⟶ A := pullback.fst j (b ≫ s)

/-- The projection from the complete pulled-back source to the new test. -/
def completeProjection : completeSource w H j hj b ⟶ Z := pullback.snd j (b ≫ s)

/-- Every coefficient map out of the joint scheme survives on the entire pulled-back source. -/
@[reassoc]
theorem complete_coefficients {Y : Scheme} (c : J ⟶ Y) :
    completeToSource w H j hj b ≫ j ≫ c =
      completeProjection w H j hj b ≫ b ≫ s ≫ c := by
  change pullback.fst j (b ≫ s) ≫ j ≫ c = pullback.snd j (b ≫ s) ≫ b ≫ s ≫ c
  rw [pullback.condition_assoc, Category.assoc]

variable (r : J ⟶ T) (hr : j ≫ r = w)
  [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [IsSeparated r]

include hr in
/-- The quotient comparison pulls back the joint source to the whole original selected source. -/
theorem comparison_source_isPullback : IsPullback (𝟙 A) e j s := by
  let _ := comparison_isOpenImmersion w H j hj r hr
  exact IsPullback.of_horiz_isIso_mono ⟨by
    rw [Category.id_comp, projection_comparison]⟩

/-- The complete new source equals the actual pullback of the old surjective quotient. -/
def completeSourceIso : pullback e b ≅ completeSource w H j hj b :=
  (show IsPullback (pullback.fst e b) (pullback.snd e b) j (b ≫ s) from by
    simpa only [Category.comp_id] using
      (IsPullback.of_hasPullback e b).paste_horiz
        (comparison_source_isPullback w H j hj r hr)).isoPullback

@[reassoc]
theorem completeSourceIso_projection : (completeSourceIso w H j hj b r hr).hom ≫
    completeProjection w H j hj b = pullback.snd e b :=
  IsPullback.isoPullback_hom_snd _

include hr in
/-- Surjectivity holds on the complete pulled-back source, with no chosen branch substituted. -/
theorem completeProjection_surjective : Surjective (completeProjection w H j hj b) := by
  rw [← (completeSourceIso w H j hj b r hr).inv_hom_id_assoc
    (completeProjection w H j hj b), completeSourceIso_projection]
  infer_instance

include hr in
/-- Etaleness survives arbitrary test and ground-base changes on that complete source. -/
theorem completeProjection_etale : Etale (completeProjection w H j hj b) := by
  let _ := projection_etale w H j hj r hr
  exact inferInstanceAs (Etale (pullback.snd j (b ≫ s)))

include hr in
omit [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [IsSeparated r] in
/-- The old coefficient equation also holds as a scheme map on the complete new source. -/
theorem complete_old_coefficients : completeToSource w H j hj b ≫ w =
    completeProjection w H j hj b ≫ b ≫ (U).ι := by
  have h := complete_coefficients w H j hj b r
  rwa [hr, comparison_toOld w H j hj r hr] at h

end FLT.Mazur.SchemeEtaleImageDenseModel
