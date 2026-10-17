/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedFiberIdeal
public import FLT.Mazur.OneGonRetainedFiberReduced
public import FLT.Mazur.ProjectiveLineValuationExtension

/-!
# Reducedness of the full collapsed polygon fiber

Every normalization restriction is radical. At each node an omitted branch
forces full ideal detection, proving radicality on the original polygon rather
than merely after normalization. The actual fiber is consequently reduced.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedFiberReduced
open PolygonCyclicAtlas PolygonOneGonContraction PolygonCollapsedFiberIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "p" => normalization K n h
local notation "q" => nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "F" => fiberIdeal K n (by omega) p q hp i
local notation "c" => Over.Hom.left (contraction K n (by omega) p q hp i)
local notation "t" => Over.Hom.left (targetNode K)

/-- The full original collapsed-fiber ideal is radical, including both boundary nodes. -/
theorem fiberIdeal_radical : (F).radical = F := by
  apply PolygonCollapsedFiberIdeal.unique K n h i
  · intro j hj
    have hr : ((F).comap (componentMap K n h j)).radical =
        (F).comap (componentMap K n h j) := by
      rw [component_omitted K n h i hj, Scheme.IdealSheafData.radical_bot,
        Scheme.nilradical_eq_bot]
    rw [IdealSheafRadicalOpen.comap_radical_eq _ _ hr, component_omitted K n h i hj]
  · have hr : ((F).comap (componentMap K n h i)).radical =
        (F).comap (componentMap K n h i) := by
      rw [component_retained, OneGonRetainedFiberReduced.retained_ideal_radical]
    rw [IdealSheafRadicalOpen.comap_radical_eq _ _ hr, component_retained]

/-- The closed subscheme of the entire collapsed chain is reduced. -/
instance fiberSubscheme_isReduced : IsReduced (F).subscheme :=
  IdealSheafRadicalOpen.subscheme_isReduced _ (fiberIdeal_radical K n h i)

/-- The actual Cartesian fiber has exactly the previously computed ideal. -/
theorem fiberInclusion_ker : (pullback.fst (c) (t)).ker = F :=
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

/-- The Cartesian fiber and its full ideal subscheme agree over the original polygon. -/
def fiberIso : pullback (c) (t) ≅ (F).subscheme :=
  asIso (pullback.fst (c) (t)).toImage ≪≫
    BaseAdicThickening.subschemeCongr (fiberInclusion_ker K n h i)

/-- The comparison retains the original fiber inclusion as a scheme morphism. -/
@[reassoc] theorem fiberIso_hom_ι :
    (fiberIso K n h i).hom ≫ (F).subschemeι = pullback.fst (c) (t) := by
  simp only [fiberIso, Iso.trans_hom, asIso_hom, Category.assoc,
    BaseAdicThickening.subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

/-- The actual Cartesian collapsed fiber is reduced, without replacing it by a reduction. -/
instance fiber_isReduced : IsReduced (pullback (c) (t)) :=
  isReduced_of_isOpenImmersion (fiberIso K n h i).hom

end FLT.Mazur.PolygonCollapsedFiberReduced
