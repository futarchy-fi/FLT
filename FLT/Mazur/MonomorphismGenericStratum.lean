/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactGenericFlatOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Whole monomorphisms on dense opens of integral target strata

Pull back an actual quasi-compact monomorphism to any prime target stratum.
Generic flatness of the entire source makes its restriction an open immersion.
Its image is an actual open subscheme, with an inverse on all scheme tests.
The image may be empty or proper; coverage of the target is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.MonomorphismGenericStratum
set_option backward.isDefEq.respectTransparency false
variable {D K : Scheme.{0}} (m : D ⟶ K) [Mono m] [QuasiCompact m]
  [LocallyOfFinitePresentation m] [IsAffine K]
  (P : Ideal Γ(K, ⊤)) [P.IsPrime]

/-- The actual integral closed target stratum, with its original coefficient map. -/
def stratumMap : Spec (.of (Γ(K, ⊤) ⧸ P)) ⟶ K :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ K.isoSpec.inv

/-- The whole inverse image of the stratum, without restricting to an affine branch. -/
def stratumProjection : pullback m (stratumMap P) ⟶ Spec (.of (Γ(K, ⊤) ⧸ P)) :=
  pullback.snd _ _

local notation "q" => stratumProjection m P

instance stratumProjection_mono : Mono q := inferInstanceAs (Mono (pullback.snd _ _))

instance stratumProjection_quasiCompact : QuasiCompact q :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

instance stratumProjection_locallyOfFinitePresentation : LocallyOfFinitePresentation q :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

local instance : CompactSpace (pullback m (stratumMap P) : Scheme) :=
  QuasiCompact.compactSpace_of_compactSpace q

/-- A nonzero denominator is constructed using every chart of the whole original source. -/
def coefficient : Γ(K, ⊤) ⧸ P := QuasiCompactGenericFlatOpen.coefficient q

omit [Mono m] in
theorem coefficient_ne_zero : coefficient m P ≠ 0 :=
  QuasiCompactGenericFlatOpen.coefficient_ne_zero q

/-- A dense principal open in the chosen integral target stratum. -/
def targetMap : Spec (.of (Localization.Away (coefficient m P))) ⟶
    Spec (.of (Γ(K, ⊤) ⧸ P)) := QuasiCompactGenericFlatOpen.targetMap q

local notation "j" => targetMap m P

instance targetMap_isOpenImmersion : IsOpenImmersion j :=
  QuasiCompactGenericFlatOpen.targetMap_isOpenImmersion q

instance targetMap_isDominant : IsDominant j :=
  QuasiCompactGenericFlatOpen.targetMap_isDominant q

/-- The full original monomorphism becomes an open immersion on this actual target open. -/
instance projection_isOpenImmersion : IsOpenImmersion (pullback.fst j q) := by
  let _ : Flat (pullback.fst j q) := QuasiCompactGenericFlatOpen.projection_flat q
  exact IsOpenImmersion.of_flat_of_mono _

/-- The exact image is open in the constructed stratum open, and may be proper or empty. -/
def imageOpen : (Spec (.of (Localization.Away (coefficient m P)))).Opens :=
  (pullback.fst j q).opensRange

/-- The entire source over the chosen stratum open represents precisely its actual image. -/
def imageIso : pullback j q ≅ (imageOpen m P).toScheme :=
  (pullback.fst j q).isoOpensRange

/-- The image identification preserves the actual projection, including scheme structure. -/
@[reassoc]
theorem imageIso_hom_ι : (imageIso m P).hom ≫ (imageOpen m P).ι = pullback.fst j q :=
  Scheme.Hom.isoOpensRange_hom_ι _

/-- The whole iterated source retains its actual original arrow. -/
def sourceToOriginal : pullback j q ⟶ D :=
  pullback.snd j q ≫ pullback.fst m (stratumMap P)

omit [Mono m] in
/-- Both successive base changes retain the actual kernel coordinate. -/
@[reassoc]
theorem sourceToOriginal_comp : sourceToOriginal m P ≫ m =
    pullback.fst j q ≫ j ≫ stratumMap P := by
  dsimp only [sourceToOriginal]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (pullback.snd j q ≫ q) ≫ stratumMap P = _
  rw [← pullback.condition, Category.assoc]

/-- The open image carries the original arrow via the actual inverse image isomorphism. -/
def imageToOriginal : (imageOpen m P).toScheme ⟶ D :=
  (imageIso m P).inv ≫ sourceToOriginal m P

/-- This is an image of the original map, with unchanged original target coefficients. -/
@[reassoc]
theorem imageToOriginal_comp : imageToOriginal m P ≫ m =
    (imageOpen m P).ι ≫ j ≫ stratumMap P := by
  rw [imageToOriginal, Category.assoc, sourceToOriginal_comp,
    ← imageIso_hom_ι, Category.assoc, Iso.inv_hom_id_assoc]

/-- Every test map into the actual image has a unique original-source lift. -/
theorem image_test_lift {Z : Scheme} (a : Z ⟶ (imageOpen m P).toScheme) :
    ∃! b : Z ⟶ pullback j q, b ≫ pullback.fst j q = a ≫ (imageOpen m P).ι := by
  refine ⟨a ≫ (imageIso m P).inv, ?_, ?_⟩
  · dsimp only
    rw [Category.assoc, ← imageIso_hom_ι, Iso.inv_hom_id_assoc]
  · intro b hb
    apply (cancel_mono (pullback.fst j q)).mp
    rw [hb, Category.assoc, ← imageIso_hom_ι, Iso.inv_hom_id_assoc]

end FLT.Mazur.MonomorphismGenericStratum
