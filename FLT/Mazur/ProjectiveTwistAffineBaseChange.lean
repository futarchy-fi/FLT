/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleUnitCocyclePullback
public import FLT.Mazur.ProjectiveSpaceAffineBaseChange
public import FLT.Mazur.ProjectiveTwistingSheaf

/-!
# Twisting sheaves under affine base change

Coefficient maps preserve the coordinate-ratio cocycle, so actual module-sheaf
pullback identifies every integer twist with the twist over the new ring.
The projective-space fiber-product comparison then transports presentations
and their twisting sheaves over opens of the source or target. In particular,
over an affine target open the presentation uses that open's coordinate ring.
No flatness hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization TopologicalSpace Opposite
open CategoryTheory.Limits
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient change preserves the pairwise standard-chart overlaps. -/
lemma coefficientMap_preimage_overlap (i j : ι) :
    coefficientMap φ ι ⁻¹ᵁ Proj.basicOpen (grading R ι) (X i * X j) =
      Proj.basicOpen (grading S ι) (X i * X j) := by
  rw [← chart_inf, ← chart_inf, Scheme.Hom.preimage_inf,
    coefficientMap_preimage_chart, coefficientMap_preimage_chart]

/-- The homogeneous-localization map on a pairwise standard-chart overlap. -/
def coefficientOverlapRingMap (i j : ι) : overlapRing R ι i j →+* overlapRing S ι i j :=
  HomogeneousLocalization.map (coefficientGradedMap φ ι) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

/-- The overlap map preserves the coordinate-ratio unit. -/
lemma coefficientOverlapRingMap_ratio (i j : ι) :
    Units.map (coefficientOverlapRingMap φ ι i j).toMonoidHom (ratioUnit R ι i j) =
      ratioUnit S ι i j := by
  apply Units.ext
  change coefficientOverlapRingMap φ ι i j (ratioUnit R ι i j) = ratioUnit S ι i j
  simp only [ratioUnit_val, toOverlap_coordinate]
  apply val_injective
  simp [coefficientOverlapRingMap, Away.mk, HomogeneousLocalization.map_mk]

/-- The overlap ring map agrees with the actual scheme map on sections. -/
lemma coefficientOverlap_appLE (i j : ι) :
    Proj.awayToSection (grading R ι) (X i * X j) ≫
      (coefficientMap φ ι).appLE _ (Proj.basicOpen (grading S ι) (X i * X j))
        (coefficientMap_preimage_overlap φ ι i j).ge =
    CommRingCat.ofHom (coefficientOverlapRingMap φ ι i j) ≫
      Proj.awayToSection (grading S ι) (X i * X j) := by
  have h (s : MvPolynomial ι S) (hs : coefficientGradedMap φ ι (X i * X j) = s) :
      Proj.awayToSection (grading R ι) (X i * X j) ≫
        (coefficientMap φ ι).appLE _ (Proj.basicOpen (grading S ι) s)
          (by rw [← hs]; rfl) =
      CommRingCat.ofHom (HomogeneousLocalization.map (coefficientGradedMap φ ι)
        (P := Submonoid.powers (X i * X j)) (Q := Submonoid.powers s) (by
          rintro _ ⟨n, rfl⟩
          exact ⟨n, by simp [← hs]⟩)) ≫ Proj.awayToSection (grading S ι) s := by
    subst s
    exact Proj.awayToSection_comp_appLE (coefficientGradedMap φ ι)
      (coefficientGradedMap_irrelevant φ ι) ((isHomogeneous_X R i).mul (isHomogeneous_X R j))
  exact h (X i * X j) (by simp)

/-- Coefficient change preserves every integer power of the transition unit. -/
lemma coefficient_transitionSection (n : ℤ) (i j : ι) :
    Units.map ((coefficientMap φ ι).appLE _ (Proj.basicOpen (grading S ι) (X i * X j))
      (coefficientMap_preimage_overlap φ ι i j).ge).hom.toMonoidHom
        (transitionSection R ι n i j) = transitionSection S ι n i j := by
  have h := congrArg (fun a ↦ Units.map a.hom.toMonoidHom (transitionUnit R ι n i j))
    (coefficientOverlap_appLE φ ι i j)
  change Units.map (((coefficientMap φ ι).appLE _ _ _).hom.toMonoidHom.comp
      (Proj.awayToSection (grading R ι) (X i * X j)).hom.toMonoidHom) _ =
    Units.map ((Proj.awayToSection (grading S ι) (X i * X j)).hom.toMonoidHom.comp
      (coefficientOverlapRingMap φ ι i j).toMonoidHom) _ at h
  simpa only [Units.map_comp, MonoidHom.comp_apply, transitionSection, transitionUnit,
    map_zpow, coefficientOverlapRingMap_ratio] using h

/-- The transition on any common subopen is the restriction of the overlap section. -/
lemma twistCocycle_unit_section (A : Type u) [CommRing A] (n : ℤ) (i j : ι)
    (V : (space A ι).Opens) (hi : V ≤ chart A ι i) (hj : V ≤ chart A ι j) :
    ((twistCocycle A ι n).unit i j V hi hj : Γ(space A ι, V)) =
      (space A ι).presheaf.map
        (homOfLE ((le_inf hi hj).trans (chart_inf A ι i j).le)).op
          (transitionSection A ι n i j : Γ(space A ι,
            Proj.basicOpen (grading A ι) (X i * X j))) := by
  change (space A ι).presheaf.map _ ((space A ι).presheaf.map _
    (transitionSection A ι n i j : Γ(space A ι,
      Proj.basicOpen (grading A ι) (X i * X j)))) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The inverse-image cocycle equals the new coefficient-ring cocycle on every subopen. -/
lemma coefficient_twistCocycle_unit (n : ℤ) (i j : ι) (V : (space S ι).Opens)
    (hi : V ≤ coefficientMap φ ι ⁻¹ᵁ chart R ι i)
    (hj : V ≤ coefficientMap φ ι ⁻¹ᵁ chart R ι j)
    (hi' : V ≤ chart S ι i) (hj' : V ≤ chart S ι j) :
    ((twistCocycle R ι n).inverseImage (coefficientMap φ ι)).unit i j V hi hj =
      (twistCocycle S ι n).unit i j V hi' hj' := by
  apply Units.ext
  change ((twistCocycle R ι n).inverseImageUnit (coefficientMap φ ι) i j V hi hj :
    Γ(space S ι, V)) = _
  rw [(twistCocycle R ι n).inverseImageUnit_eq (coefficientMap φ ι) i j V hi hj
    (chart R ι i ⊓ chart R ι j) inf_le_left inf_le_right (le_inf hi hj)]
  rw [twistCocycle_unit_section, twistCocycle_unit_section]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have ht := congrArg (fun t : Γ(space S ι,
      Proj.basicOpen (grading S ι) (X i * X j))ˣ ↦
      (space S ι).presheaf.map (homOfLE ((le_inf hi' hj').trans (chart_inf S ι i j).le)).op
        (t : Γ(space S ι, _))) (coefficient_transitionSection φ ι n i j)
  change (space S ι).presheaf.map _ ((coefficientMap φ ι).appLE _ _ _ _) = _ at ht
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at ht
  simpa only [← CommRingCat.comp_apply, ← Functor.map_comp] using ht

/-- Equal chart families and transition units give equal descended module sheaves. -/
lemma cocycleSheaf_eq {X : Scheme.{u}} {κ : Type u} {U V : κ → X.Opens}
    (g : Cocycle U) (h : Cocycle V) (hUV : U = V)
    (hu : ∀ i j W hi hj hi' hj', g.unit i j W hi hj = h.unit i j W hi' hj') :
    g.sheaf = h.sheaf := by
  subst V
  have he : g.unit = h.unit := by
    funext i j W hi hj
    exact hu i j W hi hj hi hj
  have hg : g = h := by
    cases g
    cases h
    cases he
    rfl
  exact congrArg Cocycle.sheaf hg

/-- Arbitrary coefficient change preserves every integer twisting sheaf. -/
def coefficientTwistingPullbackIso (n : ℤ) :
    (Scheme.Modules.pullback (coefficientMap φ ι)).obj (twistingSheaf R ι n) ≅
      twistingSheaf S ι n :=
  (twistCocycle R ι n).pullbackIso (coefficientMap φ ι) (iSup_chart R ι) ≪≫
    eqToIso (cocycleSheaf_eq _ _ (funext (coefficientMap_preimage_chart φ ι))
      (coefficient_twistCocycle_unit φ ι n))

/-- Arbitrary coefficient change preserves the actual hyperplane line bundle. -/
def coefficientOOnePullbackIso {A B : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (d : ℕ) :
    (Scheme.Modules.pullback (coefficientMap ψ (Fin (d + 1)))).obj (O A d 1) ≅ O B d 1 :=
  coefficientTwistingPullbackIso ψ (Fin (d + 1)) 1

open Scheme.Modules

/-- The actual fiber-product comparison carries the pulled-back twist to `O(n)`. -/
def affineBaseChangeTwistingIso {A B : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (d : ℕ) (n : ℤ) :
    (Scheme.Modules.pullback (affineBaseChangeIso ψ d).hom).obj
      ((Scheme.Modules.pullback (pullback.fst (baseProjection A (Fin (d + 1)))
        (Spec.map (CommRingCat.ofHom ψ)))).obj (O A d n)) ≅ O B d n :=
  (pullbackComp (affineBaseChangeIso ψ d).hom (pullback.fst _ _)).app _ ≪≫
    (pullbackCongr (affineBaseChangeIso_hom_fst ψ d)).app _ ≪≫
    coefficientTwistingPullbackIso ψ (Fin (d + 1)) n

/-- The coefficient homomorphism induced by a structural map on an open subscheme. -/
def openCoefficientRingMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of A)) (U : X.Opens) : A →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

/-- The open subscheme's canonical map to its spectrum lies over the original base. -/
@[reassoc]
lemma openCoefficientRingMap_square {A : Type u} [CommRing A] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of A)) (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (openCoefficientRingMap q U)) = U.ι ≫ q := by
  change U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop ≫
    X.presheaf.map (homOfLE le_top).op) = _
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc,
    ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Factor a projective presentation over the ring of sections of any open. -/
def openCoefficientMap {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) (U : X.Opens) :
    U.toScheme ⟶ space Γ(X, U) (Fin (d + 1)) :=
  pullback.lift (U.ι ≫ i) U.toSpecΓ
      (by rw [Category.assoc, openCoefficientRingMap_square]) ≫
    (affineBaseChangeIso (openCoefficientRingMap (i ≫ baseProjection A _) U) d).inv

/-- The factored presentation recovers the restriction of the original presentation. -/
@[reassoc]
lemma openCoefficientMap_comp {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) (U : X.Opens) :
    openCoefficientMap i U ≫
      coefficientMap (openCoefficientRingMap (i ≫ baseProjection A _) U) _ = U.ι ≫ i := by
  rw [openCoefficientMap, Category.assoc,
    ← affineBaseChangeIso_hom_fst (openCoefficientRingMap (i ≫ baseProjection A _) U) d,
    Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The factored presentation has the canonical structural map over the section ring. -/
@[reassoc]
lemma openCoefficientMap_baseProjection {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) (U : X.Opens) :
    openCoefficientMap i U ≫ baseProjection Γ(X, U) _ = U.toSpecΓ := by
  rw [openCoefficientMap, Category.assoc,
    ← affineBaseChangeIso_hom_snd (openCoefficientRingMap (i ≫ baseProjection A _) U) d,
    Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- Restriction and coefficient change identify the actual pulled-back twisting sheaves. -/
def openCoefficientTwistingIso {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) (U : X.Opens) (n : ℤ) :
    ((Scheme.Modules.pullback i).obj (O A d n)).restrict U.ι ≅
      (Scheme.Modules.pullback (openCoefficientMap i U)).obj (O Γ(X, U) d n) :=
  (restrictFunctorIsoPullback U.ι).app _ ≪≫
    (pullbackComp U.ι i).app _ ≪≫
    (pullbackCongr (openCoefficientMap_comp i U).symm).app _ ≪≫
    ((pullbackComp (openCoefficientMap i U)
      (coefficientMap (openCoefficientRingMap (i ≫ baseProjection A _) U) _)).app _).symm ≪≫
    (Scheme.Modules.pullback (openCoefficientMap i U)).mapIso
      (coefficientTwistingPullbackIso (openCoefficientRingMap (i ≫ baseProjection A _) U)
        (Fin (d + 1)) n)

/-- On an affine open, the transported presentation is a map from its actual spectrum. -/
def affineOpenCoefficientMap {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) {U : X.Opens} (hU : IsAffineOpen U) :
    Spec Γ(X, U) ⟶ space Γ(X, U) (Fin (d + 1)) :=
  hU.isoSpec.inv ≫ openCoefficientMap i U

/-- The affine coefficient presentation is over the identity of the section-ring spectrum. -/
@[reassoc]
lemma affineOpenCoefficientMap_baseProjection {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) {U : X.Opens} (hU : IsAffineOpen U) :
    affineOpenCoefficientMap i hU ≫ baseProjection Γ(X, U) _ = 𝟙 _ := by
  rw [affineOpenCoefficientMap, Category.assoc, openCoefficientMap_baseProjection,
    hU.isoSpec_inv_toSpecΓ]

/-- Affine-open coefficient transport for the actual restricted pullback of `O(n)`. -/
def affineOpenCoefficientTwistingIso {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) {U : X.Opens}
    (hU : IsAffineOpen U) (n : ℤ) :
    (Scheme.Modules.pullback hU.isoSpec.inv).obj
      (((Scheme.Modules.pullback i).obj (O A d n)).restrict U.ι) ≅
        (Scheme.Modules.pullback (affineOpenCoefficientMap i hU)).obj (O Γ(X, U) d n) :=
  (Scheme.Modules.pullback hU.isoSpec.inv).mapIso (openCoefficientTwistingIso i U n) ≪≫
    (pullbackComp hU.isoSpec.inv (openCoefficientMap i U)).app _

/-- In particular the hyperplane line bundle transports along every affine open. -/
def affineOpenCoefficientOOneIso {A : Type} [CommRing A] {X : Scheme}
    {d : ℕ} (i : X ⟶ space A (Fin (d + 1))) {U : X.Opens} (hU : IsAffineOpen U) :
    (Scheme.Modules.pullback hU.isoSpec.inv).obj
      (((Scheme.Modules.pullback i).obj (O A d 1)).restrict U.ι) ≅
        (Scheme.Modules.pullback (affineOpenCoefficientMap i hU)).obj (O Γ(X, U) d 1) :=
  affineOpenCoefficientTwistingIso i hU 1


/-- Lift a projective presentation across arbitrary affine coefficient change. -/
def coefficientLift {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B)
    {Z : Scheme} {d : ℕ} (a : Z ⟶ space A (Fin (d + 1))) (b : Z ⟶ Spec (.of B))
    (h : a ≫ baseProjection A _ = b ≫ Spec.map (CommRingCat.ofHom ψ)) :
    Z ⟶ space B (Fin (d + 1)) :=
  pullback.lift a b h ≫ (affineBaseChangeIso ψ d).inv

/-- Coefficient lifting preserves the original projective presentation. -/
@[reassoc]
lemma coefficientLift_comp {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B)
    {Z : Scheme} {d : ℕ} (a : Z ⟶ space A (Fin (d + 1))) (b : Z ⟶ Spec (.of B))
    (h : a ≫ baseProjection A _ = b ≫ Spec.map (CommRingCat.ofHom ψ)) :
    coefficientLift ψ a b h ≫ coefficientMap ψ _ = a := by
  rw [coefficientLift, Category.assoc, ← affineBaseChangeIso_hom_fst ψ d,
    Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- Coefficient lifting has the prescribed structural map. -/
@[reassoc]
lemma coefficientLift_baseProjection {A B : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) {Z : Scheme} {d : ℕ} (a : Z ⟶ space A (Fin (d + 1)))
    (b : Z ⟶ Spec (.of B)) (h : a ≫ baseProjection A _ = b ≫ Spec.map (CommRingCat.ofHom ψ)) :
    coefficientLift ψ a b h ≫ baseProjection B _ = b := by
  rw [coefficientLift, Category.assoc, ← affineBaseChangeIso_hom_snd ψ d,
    Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The constructed coefficient lift identifies the actual pullbacks of all twists. -/
def coefficientLiftTwistingIso {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B)
    {Z : Scheme} {d : ℕ} (a : Z ⟶ space A (Fin (d + 1))) (b : Z ⟶ Spec (.of B))
    (h : a ≫ baseProjection A _ = b ≫ Spec.map (CommRingCat.ofHom ψ)) (n : ℤ) :
    (Scheme.Modules.pullback a).obj (O A d n) ≅
      (Scheme.Modules.pullback (coefficientLift ψ a b h)).obj (O B d n) :=
  (pullbackCongr (coefficientLift_comp ψ a b h).symm).app _ ≪≫
    ((pullbackComp (coefficientLift ψ a b h) (coefficientMap ψ _)).app _).symm ≪≫
    (Scheme.Modules.pullback (coefficientLift ψ a b h)).mapIso
      (coefficientTwistingPullbackIso ψ _ n)

/-- The square defining coefficient transport over an open of the target. -/
lemma targetOpenCoefficient_square {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) :
    ((f ⁻¹ᵁ U).ι ≫ i) ≫ baseProjection A _ =
      ((f ∣_ U) ≫ U.toSpecΓ) ≫ Spec.map (CommRingCat.ofHom (openCoefficientRingMap q U)) := by
  simp only [Category.assoc, h, openCoefficientRingMap_square, morphismRestrict_ι_assoc]

/-- Present the inverse image of a target open over that target open's coordinate ring. -/
def targetOpenCoefficientMap {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶ space Γ(Y, U) (Fin (d + 1)) :=
  coefficientLift (openCoefficientRingMap q U) ((f ⁻¹ᵁ U).ι ≫ i)
    ((f ∣_ U) ≫ U.toSpecΓ) (targetOpenCoefficient_square f q i h U)

/-- The target-open presentation recovers the restricted original presentation. -/
@[reassoc]
lemma targetOpenCoefficientMap_comp {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) :
    targetOpenCoefficientMap f q i h U ≫ coefficientMap (openCoefficientRingMap q U) _ =
      (f ⁻¹ᵁ U).ι ≫ i :=
  coefficientLift_comp _ _ _ _

/-- The target-open presentation is over the canonical map to the target section ring. -/
@[reassoc]
lemma targetOpenCoefficientMap_baseProjection {A : Type} [CommRing A] {X Y : Scheme}
    {d : ℕ} (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) :
    targetOpenCoefficientMap f q i h U ≫ baseProjection Γ(Y, U) _ =
      (f ∣_ U) ≫ U.toSpecΓ :=
  coefficientLift_baseProjection _ _ _ _

/-- Restricting `i*O(n)` over a target open transports its coefficients to that open's ring. -/
def targetOpenCoefficientTwistingIso {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) (n : ℤ) :
    ((Scheme.Modules.pullback i).obj (O A d n)).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (targetOpenCoefficientMap f q i h U)).obj (O Γ(Y, U) d n) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι i).app _ ≪≫
    coefficientLiftTwistingIso (openCoefficientRingMap q U) ((f ⁻¹ᵁ U).ι ≫ i)
      ((f ∣_ U) ≫ U.toSpecΓ) (targetOpenCoefficient_square f q i h U) n

/-- On an affine target open, the structural map is the restricted map followed by `isoSpec`. -/
lemma targetAffineOpenCoefficientMap_baseProjection {A : Type} [CommRing A]
    {X Y : Scheme} {d : ℕ} (f : X ⟶ Y) (q : Y ⟶ Spec (.of A))
    (i : X ⟶ space A (Fin (d + 1))) (h : i ≫ baseProjection A _ = f ≫ q)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    targetOpenCoefficientMap f q i h U ≫ baseProjection Γ(Y, U) _ =
      (f ∣_ U) ≫ hU.isoSpec.hom :=
  targetOpenCoefficientMap_baseProjection f q i h U

/-- The affine-target coefficient isomorphism for the hyperplane line bundle. -/
def targetAffineOpenCoefficientOOneIso {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
    (h : i ≫ baseProjection A _ = f ≫ q) (U : Y.Opens) :
    ((Scheme.Modules.pullback i).obj (O A d 1)).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (targetOpenCoefficientMap f q i h U)).obj (O Γ(Y, U) d 1) :=
  targetOpenCoefficientTwistingIso f q i h U 1

end FLT.Mazur.ProjectiveSpace
