/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPushforwardRestriction
public import FLT.Mazur.ProjectiveSerrePresentationTower
public import FLT.Mazur.ProjectiveTwistAffineBaseChange

/-!
# Localization of a fixed Serre presentation tower

Restriction transports the chosen short exact sequences and finite sums of
negative twists. The resulting tower keeps the original length and degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.ProjectiveSpace

/-- A tower with explicit short exact sequences and identified negative-twist terms.
The first term of each sequence is the actual kernel, up to its specified exact sequence. -/
inductive ExactTwistTower (R : Type) [CommRing R] (ι : Type) :
    (space R ι).Modules → ℕ → Type 1
  | zero (F : (space R ι).Modules) : ExactTwistTower R ι F 0
  | step {F : (space R ι).Modules} {c : ℕ}
      (d : ℕ) (κ : Type) (finite : Finite κ)
      (S : ShortComplex (space R ι).Modules) (coherent : CoherentDevissage.CoherentSequence S)
      (source : S.X₂ ≅ ∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ)))
      (target : S.X₃ ≅ F) (tail : ExactTwistTower R ι S.X₁ c) :
      ExactTwistTower R ι F (c + 1)

/-- The degrees of the fixed tower, in presentation order. -/
def TwistPresentationTower.degrees {R : Type} [CommRing R] {ι : Type}
    {F : (space R ι).Modules} {c : ℕ} (T : TwistPresentationTower R ι F c) : List ℕ :=
  match T with
  | .zero _ => []
  | .step d _ _ _ _ tail => d :: tail.degrees

/-- The degrees retained in a transported tower. -/
def ExactTwistTower.degrees {R : Type} [CommRing R] {ι : Type}
    {F : (space R ι).Modules} {c : ℕ} (T : ExactTwistTower R ι F c) : List ℕ :=
  match T with
  | .zero _ => []
  | .step d _ _ _ _ _ _ tail => d :: tail.degrees

/-- The maximum degree of the transported tower. -/
def ExactTwistTower.bound {R : Type} [CommRing R] {ι : Type}
    {F : (space R ι).Modules} {c : ℕ} (T : ExactTwistTower R ι F c) : ℕ :=
  match T with
  | .zero _ => 0
  | .step d _ _ _ _ _ _ tail => max d tail.bound

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type)

/-- A coefficient map over an open immersion of affine bases is itself an open immersion. -/
lemma coefficientMap_isOpenImmersion [Finite ι]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    IsOpenImmersion (coefficientMap φ ι) :=
  MorphismProperty.of_isPullback (coefficient_isPullback_of_finite φ ι).flip
    (inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))))

variable [IsOpenImmersion (coefficientMap φ ι)]

/-- Restriction is exact, so the original kernel sequences remain short exact. -/
lemma coefficientRestrict_shortExact (C : ShortComplex (space R ι).Modules)
    (hC : C.ShortExact) : (C.map (restrictFunctor (coefficientMap φ ι))).ShortExact :=
  hC.map_of_exact _

/-- The restricted sequences retain coherence as well as exactness. -/
lemma coefficientRestrict_coherent (C : ShortComplex (space R ι).Modules)
    (hC : CoherentDevissage.CoherentSequence C) :
    CoherentDevissage.CoherentSequence (C.map (restrictFunctor (coefficientMap φ ι))) := by
  let := hC.finite₁
  let := hC.finite₂
  let := hC.finite₃
  exact ⟨coefficientRestrict_shortExact φ ι C hC.shortExact,
    coherent_restrict _ _, coherent_restrict _ _, coherent_restrict _ _⟩

/-- Finite twist sums retain their index and integer degree after coefficient restriction. -/
def coefficientRestrictTwistSumIso (κ : Type) (d : ℤ) :
    (∐ fun _ : κ ↦ twistingSheaf R ι d).restrict (coefficientMap φ ι) ≅
      ∐ fun _ : κ ↦ twistingSheaf S ι d :=
  PreservesCoproduct.iso (restrictFunctor (coefficientMap φ ι)) _ ≪≫
    Sigma.mapIso (fun _ ↦ (restrictFunctorIsoPullback (coefficientMap φ ι)).app _ ≪≫
      coefficientTwistingPullbackIso φ ι d)

/-- Transport the same chosen tower; no presentation is selected over the new base. -/
def localizeTower {F : (space R ι).Modules} {c : ℕ}
    (T : TwistPresentationTower R ι F c) :
    ExactTwistTower S ι (F.restrict (coefficientMap φ ι)) c :=
  match T with
  | .zero F => .zero _
  | .step d κ hκ p hp tail =>
    .step d κ hκ ((ShortComplex.kernelSequence p).map
      (restrictFunctor (coefficientMap φ ι)))
      (coefficientRestrict_coherent φ ι _ hp)
      (coefficientRestrictTwistSumIso φ ι κ (-(d : ℤ))) (Iso.refl _)
      (localizeTower tail)

/-- Localization preserves every degree, not merely an upper bound. -/
lemma localizeTower_degrees {F : (space R ι).Modules} {c : ℕ}
    (T : TwistPresentationTower R ι F c) : (localizeTower φ ι T).degrees = T.degrees := by
  induction T with
  | zero => rfl
  | step d κ hκ p hp tail ih => exact congrArg (List.cons d) ih

/-- The uniform numerical bound is unchanged under localization. -/
lemma localizeTower_bound {F : (space R ι).Modules} {c : ℕ}
    (T : TwistPresentationTower R ι F c) : (localizeTower φ ι T).bound = T.bound := by
  induction T with
  | zero => rfl
  | step d κ hκ p hp tail ih => exact congrArg (max d) ih

/-- The scalar maps in an open cartesian square agree on corresponding opens. -/
lemma openBaseChange_scalar {X Y U V : Scheme} (f : X ⟶ Y) (g : U ⟶ V)
    (i : U ⟶ X) (j : V ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (H : IsPullback g i j f) (W : V.Opens) :
    (j.appIso W).inv ≫ f.app (j ''ᵁ W) ≫
      X.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op =
      g.app W ≫ (i.appIso (g ⁻¹ᵁ W)).inv := by
  apply (cancel_epi (j.appIso W).hom).mp
  apply (cancel_mono (i.appIso (g ⁻¹ᵁ W)).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE, H.w]

/-- Underived coefficient base change, constructed from the actual open cartesian square. -/
def openPushforwardBaseChange {X Y U V : Scheme} (f : X ⟶ Y) (g : U ⟶ V)
    (i : U ⟶ X) (j : V ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (H : IsPullback g i j f) :
    pushforward f ⋙ restrictFunctor j ≅ restrictFunctor i ⋙ pushforward g := by
  have : (j.opensFunctor ⋙ TopologicalSpace.Opens.map f.base).IsContinuous
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Y) _
  have : (TopologicalSpace.Opens.map g.base ⋙ i.opensFunctor).IsContinuous
      (Opens.grothendieckTopology V)
      (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology U) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · exact NatIso.ofComponents (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W))
      (by cat_disch)
  · ext W x
    exact congrArg (fun k ↦ k.hom x) (openBaseChange_scalar f g i j H W.unop)

/-- Principal coefficient localization is an open immersion. -/
instance principalCoefficient_isOpenImmersion (R : Type) [CommRing R]
    (ι : Type) [Finite ι] (r : R) :
    IsOpenImmersion (coefficientMap (algebraMap R (Localization.Away r)) ι) :=
  coefficientMap_isOpenImmersion _ _

/-- The inverse image of the principal affine-base open. -/
abbrev principalSource {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) : Y.Opens :=
  (i ≫ baseProjection R _) ⁻¹ᵁ PrimeSpectrum.basicOpen r

/-- The structural map from the principal source to the actual localized spectrum. -/
def principalBaseMap {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) :
    (principalSource i r).toScheme ⟶ Spec (.of (Localization.Away r)) :=
  ((i ≫ baseProjection R _) ∣_ PrimeSpectrum.basicOpen r) ≫
    (basicOpenIsoSpecAway (R := .of R) r).hom

/-- The localized structural square commutes. -/
lemma principalBaseMap_square {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) :
    ((principalSource i r).ι ≫ i) ≫ baseProjection R _ =
      principalBaseMap i r ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r))) := by
  dsimp only [principalBaseMap]
  simp only [Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap, morphismRestrict_ι]

/-- The closed projective presentation over the principal localization. -/
def principalEmbedding {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) :
    (principalSource i r).toScheme ⟶ space (Localization.Away r) (Fin (d + 1)) :=
  coefficientLift (algebraMap R (Localization.Away r))
    ((principalSource i r).ι ≫ i) (principalBaseMap i r) (principalBaseMap_square i r)

/-- Principal localization gives the cartesian square of projective presentations. -/
lemma principalEmbedding_isPullback {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) :
    IsPullback (principalEmbedding i r) (principalSource i r).ι
      (coefficientMap (algebraMap R (Localization.Away r)) _) i := by
  have H : IsPullback (principalBaseMap i r) (principalSource i r).ι
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))
      (i ≫ baseProjection R _) := by
    apply IsOpenImmersion.isPullback
    · exact (Category.assoc _ _ _).symm.trans (principalBaseMap_square i r)
    · rw [Scheme.Opens.opensRange_ι]
      congr 1
      exact (TopologicalSpace.Opens.ext
        (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).symm).symm
  apply IsPullback.of_right (t := (coefficient_isPullback
    (algebraMap R (Localization.Away r)) d).flip)
  · simpa only [principalEmbedding, coefficientLift_baseProjection] using H
  · exact coefficientLift_comp _ _ _ _

instance principalEmbedding_isClosedImmersion {R : Type} [CommRing R]
    {Y : Scheme} {d : ℕ} (i : Y ⟶ space R (Fin (d + 1))) [IsClosedImmersion i] (r : R) :
    IsClosedImmersion (principalEmbedding i r) :=
  MorphismProperty.of_isPullback (principalEmbedding_isPullback i r).flip inferInstance

/-- Closed coefficients commute with principal localization through the constructed square. -/
def principalClosedCoefficientIso {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) (F : Y.Modules) :
    ((pushforward i).obj F).restrict
      (coefficientMap (algebraMap R (Localization.Away r)) _) ≅
    (pushforward (principalEmbedding i r)).obj (F.restrict (principalSource i r).ι) :=
  (openPushforwardBaseChange i (principalEmbedding i r) (principalSource i r).ι
    (coefficientMap (algebraMap R (Localization.Away r)) _)
    (principalEmbedding_isPullback i r)).app F

/-- Every pulled-back integer twist has the required principal-local coefficient comparison. -/
def principalTwistingIso {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (r : R) (n : ℤ) :
    ((Scheme.Modules.pullback i).obj (O R d n)).restrict (principalSource i r).ι ≅
      (Scheme.Modules.pullback (principalEmbedding i r)).obj (O (Localization.Away r) d n) :=
  (restrictFunctorIsoPullback (principalSource i r).ι).app _ ≪≫
    (pullbackComp (principalSource i r).ι i).app _ ≪≫
    coefficientLiftTwistingIso (algebraMap R (Localization.Away r))
      ((principalSource i r).ι ≫ i) (principalBaseMap i r) (principalBaseMap_square i r) n

end FLT.Mazur.ProjectiveSpace
