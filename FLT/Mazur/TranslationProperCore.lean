/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCoreResidualInterior
public import FLT.Mazur.ProperTranslationNeighborhoodInterior

/-!
# Independent envelope cores from actual proper translation opens

Pull back the translation open along the actual second projection. Cartesian
pasting proves the resulting core proper over the original source. Its
complement retains every independent residual coordinate, and its excluded
image gives the exact obstruction to the original full interior.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.TranslationProperCore
open SchemeOpenEnvelope ProperCoreResidualInterior
universe u
variable {S : Scheme.{u}} (B W : Over S) (T : W.left.Opens)
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "ρ" => Over.Hom.left (prod.snd : prod B W ⟶ W)

/-- The actual independent envelope core retains all points with translation coordinate in `T`. -/
def core : (prod B W).left.Opens := ρ ⁻¹ᵁ T

/-- The core projection is a base change of the restricted translation structural map. -/
theorem core_isPullback :
    IsPullback (ρ ∣_ T) ((core B W T).ι ≫ π) (T.ι ≫ W.hom) B.hom :=
  (isPullback_morphismRestrict ρ T).paste_vert
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B W)).flip

instance core_projection_isProper [IsProper (T.ι ≫ W.hom)] :
    IsProper ((core B W T).ι ≫ π) :=
  MorphismProperty.of_isPullback (core_isPullback B W T) inferInstance

instance core_projection_isFinite [IsFinite (T.ι ≫ W.hom)] :
    IsFinite ((core B W T).ι ≫ π) :=
  MorphismProperty.of_isPullback (core_isPullback B W T) inferInstance

/-- Whole translation-fiber coverage covers every independent envelope point over that ground. -/
theorem fiber_subset_core (s : S) (hT : ∀ w : W.left, W.hom w = s → w ∈ T)
    (x : B.left) (hx : B.hom x = s) :
    ∀ y : (prod B W).left, π y = x → y ∈ core B W T := by
  intro y hy
  apply hT
  have h : ρ ≫ W.hom = π ≫ B.hom :=
    (prod.snd : prod B W ⟶ W).w.trans (prod.fst : prod B W ⟶ B).w.symm
  change (ρ ≫ W.hom) y = s
  rw [h, Scheme.Hom.comp_apply, hy, hx]

variable (U : (prod B W).left.Opens) [IsProper (T.ι ≫ W.hom)]

omit [IsProper (T.ι ≫ W.hom)] in
/-- The residual bad image uses every original envelope point outside the translation core. -/
theorem residualBadImage_eq :
    residualBadImage π U (core B W T) =
      π '' {y : (prod B W).left | y ∉ U ∧ ρ y ∉ T} := rfl

/-- The proper core leaves precisely the closure of the excluded residual-coordinate image. -/
theorem mem_fullInterior_iff (x : B.left) (hx : x ∈ fullFiberLocus π U) :
    x ∈ fullFiberInterior π U ↔
      x ∉ closure (π '' {y : (prod B W).left | y ∉ U ∧ ρ y ∉ T}) :=
  mem_fullFiberInterior_iff π U (core B W T) x hx

/-- Actual original denominators follow when a finite full-fiber family avoids that closure. -/
theorem exists_original_denominator [IsAffine B.left] (F : Set B.left) (hF : F.Finite)
    (hFU : F ⊆ fullFiberLocus π U)
    (hr : Disjoint F (closure (π '' {y : (prod B W).left | y ∉ U ∧ ρ y ∉ T}))) :
    ∃ r : Γ(B.left, ⊤), F ⊆ B.left.basicOpen r ∧ r ∈ denominatorIdeal (π).appTop.hom U :=
  exists_denominator π U (core B W T) F hF hFU hr

end FLT.Mazur.TranslationProperCore
