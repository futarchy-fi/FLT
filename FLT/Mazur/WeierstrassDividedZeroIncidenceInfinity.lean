/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSlope
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSections
public import FLT.Mazur.WeierstrassModificationXIncidenceLineSections

/-!
# The exact start-zero incidence and infinity intersection

The first retained incidence line meets the original infinity chart along
its whole two-root complement. The cartesian square uses the actual original
attachment, and the two markings are the retained start-zero node sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk
local notation "i" => finiteInfinityTensorChart hπ data K (j + 1 + r) hr
local notation "L" => olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk

/-- The whole original slope chart is the cartesian infinity boundary of the first fiber. -/
theorem zeroRetainedSlopeInfinity_isPullback :
    IsPullback t (s ≫ fiberIncidenceImmersion a c) i g := by
  apply (olderGlobalZeroInfinity_isPullback hπ data D j hj r hr hk0 hk).of_iso'
    (fiberInfinitySlopeIso a c) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [fiberInfinitySlopeIso_inclusion]
    exact (fiberExteriorSlopeChart_incidence a c).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

instance zeroRetainedSlopeToInfinity_isOpenImmersion : IsOpenImmersion t :=
  MorphismProperty.of_isPullback
    (zeroRetainedSlopeInfinity_isPullback hπ data D j hj r hr hk0 hk).flip
    (show IsOpenImmersion g from inferInstance)

/-- The entire retained incidence line meets infinity in precisely its two-root complement. -/
theorem zeroRetainedIncidenceInfinity_isPullback : IsPullback t s i L := by
  have H : IsPullback (𝟙 _) s (s ≫ fiberIncidenceImmersion a c)
      (fiberIncidenceImmersion a c) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, olderGlobalZeroIncidence] using
    H.paste_horiz (zeroRetainedSlopeInfinity_isPullback hπ data D j hj r hr hk0 hk)

/-- The original gluing square retains the complete incidence-line inclusion. -/
@[reassoc] theorem zeroRetainedIncidenceInfinity_comp : t ≫ i = s ≫ L :=
  (zeroRetainedIncidenceInfinity_isPullback hπ data D j hj r hr hk0 hk).w

/-- The first incidence marking is the original first retained start-zero node. -/
@[reassoc] theorem zeroRetainedIncidence_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫ L =
      olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroIncidence,
    incidenceLineFirstSection_spec_assoc a c (D.a₁_unit.map (residue R))]
  rfl

/-- The second marking is the original second retained node, with slope minus a₁. -/
@[reassoc] theorem zeroRetainedIncidence_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫ L =
      olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroIncidence,
    incidenceLineSecondSection_spec_assoc a c (D.a₁_unit.map (residue R))]
  rfl

/-- The entire retained line keeps the original residue coefficient map. -/
@[reassoc] theorem zeroRetainedIncidence_structure :
    L ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
  rw [olderGlobalZeroIncidence, Category.assoc, olderGlobalZeroSuccessiveChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fiberIncidenceMap a c).commutes)

end FLT.Mazur.WeierstrassDividedDepth
