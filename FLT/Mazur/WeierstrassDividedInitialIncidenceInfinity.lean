/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorInfinityIntersection
public import FLT.Mazur.WeierstrassDividedInitialIncidenceLine
public import FLT.Mazur.WeierstrassModificationXResidueInfinityBoundary
public import FLT.Mazur.WeierstrassModificationXFiberExteriorGeometry

/-!
# The full exterior incidence line meets infinity in its original punctured slope

The complete initial infinity localization normalizes to the same slope open
on the incidence line. These are exact scheme intersections at every retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj

local notation "g" => initialGlobalResidueFiberChart hπ data D j hj hstart hk
local notation "i" => finiteInfinityTensorChart hπ data K j hj
local notation "b" => PrincipalOpenTransport.inclusion (fiberConicFactor a c * fiberV a c)
local notation "s" => Spec.map (CommRingCat.ofHom
  (algebraMap (Polynomial K) (SlopeOpen a)))
local notation "L" => initialGlobalIncidenceLine hπ data D j hj hstart hk

/-- The full normalized original infinity boundary maps to the actual infinity tensor chart. -/
def initialGlobalResidueToInfinity :=
  (residueInfinityBoundaryIso D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)).hom ≫
      initialGlobalYToInfinity hπ data K j hj

/-- The original initial infinity square stays cartesian in full residue normal coordinates. -/
theorem initialGlobalResidueInfinity_isPullback :
    IsPullback (initialGlobalResidueToInfinity hπ data D j hj hstart hk) b i g := by
  have H := IsPullback.of_horiz_isIso (CategoryTheory.CommSq.mk
    (residueInfinityBoundaryIso_inclusion D start hstart hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)))
  exact H.paste_horiz (initialGlobalTensor_infinity_isPullback hπ data K j hj)

/-- The complete twice-punctured incidence slope line maps to the retained infinity chart. -/
def initialGlobalSlopeToInfinity :=
  (fiberInfinitySlopeIso a c).hom ≫
    initialGlobalResidueToInfinity hπ data D j hj hstart hk

/-- The entire slope open is the intersection of infinity with the whole initial residue chart. -/
theorem initialGlobalSlopeInfinity_isPullback :
    IsPullback (initialGlobalSlopeToInfinity hπ data D j hj hstart hk)
      (s ≫ fiberIncidenceImmersion a c) i g := by
  apply (initialGlobalResidueInfinity_isPullback hπ data D j hj hstart hk).of_iso'
    (fiberInfinitySlopeIso a c) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [fiberInfinitySlopeIso_inclusion, fiberExteriorSlopeChart_incidence]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The actual infinity attachment is an open immersion from the full slope open. -/
instance initialGlobalSlopeToInfinity_isOpenImmersion :
    IsOpenImmersion (initialGlobalSlopeToInfinity hπ data D j hj hstart hk) :=
  MorphismProperty.of_isPullback
    (initialGlobalSlopeInfinity_isPullback hπ data D j hj hstart hk).flip
    (show IsOpenImmersion g from inferInstance)

/-- The entire exterior incidence line meets infinity in exactly the two-root complement. -/
theorem initialGlobalIncidenceInfinity_isPullback :
    IsPullback (initialGlobalSlopeToInfinity hπ data D j hj hstart hk) s i L := by
  have T : IsPullback (𝟙 _) s (s ≫ fiberIncidenceImmersion a c)
      (fiberIncidenceImmersion a c) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, initialGlobalIncidenceLine] using
    T.paste_horiz (initialGlobalSlopeInfinity_isPullback hπ data D j hj hstart hk)

/-- The full exterior overlap retains both original actual inclusions. -/
@[reassoc] theorem initialGlobalSlopeToInfinity_comp :
    initialGlobalSlopeToInfinity hπ data D j hj hstart hk ≫ i = s ≫ L :=
  (initialGlobalIncidenceInfinity_isPullback hπ data D j hj hstart hk).w

end FLT.Mazur.WeierstrassDividedDepth
