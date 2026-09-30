/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalIdealPower
public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.IdealPowerCompatibility

/-!
# Compatibility of the actual ideal-action images

Affine image calculations construct canonical comparisons. Every comparison is
characterized by its composite with the original module inclusion.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.ModuleSubobjectCoverEquality
open FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.GlobalIdealPowerCompatibility

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {X Y Z : Scheme.{u}}

/-- Affine image containment constructs a factorization on the whole scheme. -/
def affineFactor {L N F : X.Modules} (f : L ⟶ F) (g : N ⟶ F) [Mono g]
    (h : ∀ V : X.affineOpens,
      LinearMap.range (f.val.app (op V.1)).hom ≤ LinearMap.range (g.val.app (op V.1)).hom) :
    L ⟶ N := factor f g (sections_of_local f g (by
  intro V s x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact ⟨W, hWV, hxW, h ⟨W, hW⟩ ⟨res L hWV s, rfl⟩⟩))

@[reassoc (attr := simp)]
lemma affineFactor_comp {L N F : X.Modules} (f : L ⟶ F) (g : N ⟶ F) [Mono g]
    (h : ∀ V : X.affineOpens,
      LinearMap.range (f.val.app (op V.1)).hom ≤ LinearMap.range (g.val.app (op V.1)).hom) :
    affineFactor f g h ≫ g = f := factor_comp _ _ _

/-- Equal affine images give the unique isomorphism preserving both inclusions. -/
def affineImageIso {L N F : X.Modules} (f : L ⟶ F) (g : N ⟶ F) [Mono f] [Mono g]
    (h : ∀ V : X.affineOpens,
      LinearMap.range (f.val.app (op V.1)).hom = LinearMap.range (g.val.app (op V.1)).hom) :
    L ≅ N where
  hom := affineFactor f g (fun V ↦ (h V).le)
  inv := affineFactor g f (fun V ↦ (h V).ge)
  hom_inv_id := by apply (cancel_mono f).mp; simp
  inv_hom_id := by apply (cancel_mono g).mp; simp

@[reassoc (attr := simp)]
lemma affineImageIso_comp {L N F : X.Modules} (f : L ⟶ F) (g : N ⟶ F)
    [Mono f] [Mono g] (h : ∀ V : X.affineOpens,
      LinearMap.range (f.val.app (op V.1)).hom = LinearMap.range (g.val.app (op V.1)).hom) :
    (affineImageIso f g h).hom ≫ g = f := affineFactor_comp f g (fun V ↦ (h V).le)

/-- Ideal multiples transport along a semilinear equivalence of coefficient modules. -/
lemma smul_top_transport {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (g : M ≃ₛₗ[(e : R →+* S)] N) (J : Ideal S) (x : M) :
    x ∈ J.comap e • (⊤ : Submodule R M) ↔ g x ∈ J • (⊤ : Submodule S N) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [g.map_smulₛₗ]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro hx
    suffices h : g.symm (g x) ∈ J.comap e • (⊤ : Submodule R M) by simpa using h
    refine Submodule.smul_induction_on hx (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [g.symm.map_smulₛₗ]
      exact Submodule.smul_mem_smul (by
        change e (e.symm r) ∈ J
        rwa [e.apply_symm_apply]) Submodule.mem_top
    · simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Restricting the constructed image has the affine image of the pulled-back ideal. -/
lemma restrict_range [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] (V : Y.affineOpens) :
    LinearMap.range (((restrictFunctor j).map (inclusion I F)).val.app (op V.1)).hom =
      (I.comap j).ideal V • (⊤ : Submodule Γ(Y, V.1) Γ(F.restrict j, V.1)) := by
  let W : X.affineOpens := ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  ext x
  have h := smul_top_transport (j.appIso V.1).commRingCatIsoToRingEquiv.symm
    (ModuleSheafTensor.restrictSectionsEquiv F j V.1) (I.ideal W) x
  change (∃ t, (inclusion I F).app W.1 t = x) ↔ _
  change x ∈ LinearMap.range ((inclusion I F).val.app (op W.1)).hom ↔ _
  rw [inclusion_range I F W]
  exact h.symm

/-- The ideal-action image commutes with an actual open-immersion restriction. -/
def restrictIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] :
    (multiple I F).restrict j ≅ multiple (I.comap j) (F.restrict j) := by
  have := LocallyOfFiniteType.isLocallyNoetherian j
  have := coherentPresentation_restrict j F
  exact affineImageIso ((restrictFunctor j).map (inclusion I F))
    (inclusion (I.comap j) (F.restrict j)) (fun V ↦ by
      rw [restrict_range, inclusion_range])

@[reassoc (attr := simp)]
lemma restrictIso_comp [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] :
    (restrictIso I F j).hom ≫ inclusion (I.comap j) (F.restrict j) =
      (restrictFunctor j).map (inclusion I F) := by
  unfold restrictIso
  apply affineImageIso_comp

/-- The restriction comparison uses the actual semilinear affine section transport. -/
lemma restrictIso_affine [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] (V : Y.affineOpens)
    (s : Γ((multiple I F).restrict j, V.1)) :
    (inclusion (I.comap j) (F.restrict j)).app V.1 ((restrictIso I F j).hom.app V.1 s) =
      (inclusion I F).app (j ''ᵁ V.1) s := congr($(restrictIso_comp I F j).app V.1 s)

/-- Higher ideal powers canonically include into lower powers. -/
def transition [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] {a b : ℕ} (h : a ≤ b) : power I b F ⟶ power I a F :=
  affineFactor (inclusion (I ^ b) F) (inclusion (I ^ a) F) (fun V ↦ by
    rw [inclusion_range, inclusion_range]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h))

@[reassoc (attr := simp)]
lemma transition_comp [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] {a b : ℕ} (h : a ≤ b) :
    transition I F h ≫ inclusion (I ^ a) F = inclusion (I ^ b) F := by
  unfold transition
  apply affineFactor_comp

/-- The transition agrees with B2's coefficient-submodule inclusion. -/
lemma transition_spec {R : CommRingCat.{u}} [IsNoetherianRing R]
    (I : (Spec R).IdealSheafData) (F : (Spec R).Modules) [F.IsFinitePresentation]
    {a b : ℕ} (h : a ≤ b) :
    transition I F h ≫ (specPowerIso I a F).hom =
      (specPowerIso I b F).hom ≫ IdealPowerCompatibility.powerTransition F (specIdeal I) h := by
  apply (cancel_mono (AffineIdealPowerExtension.powerMultipleι F (specIdeal I) a)).mp
  simp only [Category.assoc, specPowerIso_inclusion, transition_comp,
    IdealPowerCompatibility.powerTransition_comp]

/-- The image of two successive multiples is the product ideal acting on the original sheaf. -/
lemma nested_range [IsLocallyNoetherian X] (I J : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] (V : X.affineOpens) :
    LinearMap.range ((inclusion J (multiple I F) ≫ inclusion I F).val.app (op V.1)).hom =
      (J * I).ideal V • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1)) := by
  change LinearMap.range (((inclusion I F).val.app (op V.1)).hom.comp
    ((inclusion J (multiple I F)).val.app (op V.1)).hom) = _
  rw [LinearMap.range_comp, inclusion_range, Submodule.map_smul'', Submodule.map_top,
    inclusion_range]
  exact (Submodule.mul_smul _ _ _).symm

/-- Successive action images identify with the image of the product ideal. -/
def nestedIso [IsLocallyNoetherian X] (I J : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] : multiple J (multiple I F) ≅ multiple (J * I) F :=
  affineImageIso (inclusion J (multiple I F) ≫ inclusion I F) (inclusion (J * I) F)
    (fun V ↦ by rw [nested_range, inclusion_range])

@[reassoc (attr := simp)]
lemma nestedIso_comp [IsLocallyNoetherian X] (I J : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] :
    (nestedIso I J F).hom ≫ inclusion (J * I) F =
      inclusion J (multiple I F) ≫ inclusion I F := by
  unfold nestedIso
  apply affineImageIso_comp

/-- Nested powers have the single sum exponent, with no chosen identification as input. -/
def nestedPowerIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (a b : ℕ) (F : X.Modules)
    [F.IsFinitePresentation] : power I b (power I a F) ≅ power I (a + b) F :=
  affineImageIso (inclusion (I ^ b) (power I a F) ≫ inclusion (I ^ a) F)
    (inclusion (I ^ (a + b)) F) (fun V ↦ by
      rw [nested_range, inclusion_range]
      change ((I.ideal V) ^ b * (I.ideal V) ^ a) • _ = (I.ideal V) ^ (a + b) • _
      rw [← pow_add, Nat.add_comm])

@[reassoc]
lemma nestedPowerIso_comp [IsLocallyNoetherian X] (I : X.IdealSheafData) (a b : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] :
    (nestedPowerIso I a b F).hom ≫ inclusion (I ^ (a + b)) F =
      inclusion (I ^ b) (power I a F) ≫ inclusion (I ^ a) F := by
  unfold nestedPowerIso
  apply affineImageIso_comp

/-- Pullback along an open immersion preserves powers of the actual ideal data. -/
lemma comap_pow (I : X.IdealSheafData) (n : ℕ) (j : Y ⟶ X) [IsOpenImmersion j] :
    (I ^ n).comap j = (I.comap j) ^ n := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change ((I.ideal ⟨_, V.2.image_of_isOpenImmersion j⟩) ^ n).comap
    (j.appIso V.1).inv.hom = ((I.comap j).ideal V) ^ n
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let e := (j.appIso V.1).commRingCatIsoToRingEquiv
  let J := I.ideal ⟨_, V.2.image_of_isOpenImmersion j⟩
  change (J ^ n).comap e.symm = (J.comap e.symm) ^ n
  rw [← Ideal.map_comap_of_equiv, ← Ideal.map_comap_of_equiv, Ideal.map_pow]

/-- Restriction in the ordinary power notation, including the pulled-back exponent. -/
def powerRestrictIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] :
    (power I n F).restrict j ≅ power (I.comap j) n (F.restrict j) := by
  have := LocallyOfFiniteType.isLocallyNoetherian j
  have := coherentPresentation_restrict j F
  exact affineImageIso ((restrictFunctor j).map (inclusion (I ^ n) F))
    (inclusion ((I.comap j) ^ n) (F.restrict j)) (fun V ↦ by
      rw [restrict_range, inclusion_range, comap_pow])

@[reassoc (attr := simp)]
lemma powerRestrictIso_comp [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] :
    (powerRestrictIso I n F j).hom ≫ inclusion ((I.comap j) ^ n) (F.restrict j) =
      (restrictFunctor j).map (inclusion (I ^ n) F) := by
  unfold powerRestrictIso
  apply affineImageIso_comp

/-- Nested-power identification still commutes with inclusion after every restriction. -/
lemma nestedPowerIso_restrict [IsLocallyNoetherian X] (I : X.IdealSheafData) (a b : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j] :
    (restrictFunctor j).map (nestedPowerIso I a b F).hom ≫
      (powerRestrictIso I (a + b) F j).hom ≫
        inclusion ((I.comap j) ^ (a + b)) (F.restrict j) =
      (restrictFunctor j).map (inclusion (I ^ b) (power I a F)) ≫
        (restrictFunctor j).map (inclusion (I ^ a) F) := by
  rw [powerRestrictIso_comp, ← Functor.map_comp, nestedPowerIso_comp, Functor.map_comp]

/-- Successive constructed comparisons agree with the comparison for the composite immersion. -/
lemma powerRestrictIso_twice [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] (j : Y ⟶ X) [IsOpenImmersion j]
    (k : Z ⟶ Y) [IsOpenImmersion k] :
    have := LocallyOfFiniteType.isLocallyNoetherian j
    have := coherentPresentation_restrict j F
    (restrictFunctorComp k j).hom.app (power I n F) ≫
      (restrictFunctor k).map (powerRestrictIso I n F j).hom ≫
        (powerRestrictIso (I.comap j) n (F.restrict j) k).hom ≫
          inclusion (((I.comap j).comap k) ^ n) ((F.restrict j).restrict k) =
      (powerRestrictIso I n F (k ≫ j)).hom ≫ inclusion ((I.comap (k ≫ j)) ^ n)
        (F.restrict (k ≫ j)) ≫ (restrictFunctorComp k j).hom.app F := by
  have := LocallyOfFiniteType.isLocallyNoetherian j
  have := coherentPresentation_restrict j F
  dsimp only
  rw [powerRestrictIso_comp, ← Functor.map_comp, powerRestrictIso_comp,
    ← Category.assoc, powerRestrictIso_comp]
  exact ((restrictFunctorComp k j).hom.naturality (inclusion (I ^ n) F)).symm

/-- The unit ideal acts surjectively, so its image inclusion is invertible. -/
instance inclusion_top_isIso [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsFinitePresentation] : IsIso (inclusion (⊤ : X.IdealSheafData) F) := by
  let e := affineImageIso (inclusion (⊤ : X.IdealSheafData) F) (𝟙 F) (fun V ↦ by
    rw [inclusion_range]
    change (⊤ : Ideal Γ(X, V.1)) • ⊤ = LinearMap.range (LinearMap.id)
    simp)
  have he : e.hom = inclusion (⊤ : X.IdealSheafData) F := by
    have he : e.hom ≫ 𝟙 F = inclusion (⊤ : X.IdealSheafData) F := by
      dsimp only [e]
      apply affineImageIso_comp
    simpa using he
  rw [← he]
  infer_instance

/-- The open complement of the actual ideal support. -/
abbrev complement (I : X.IdealSheafData) : X.Opens := I.support.compl

/-- The ideal restricts to the unit ideal on the complement of its support. -/
lemma comap_complement (I : X.IdealSheafData) : I.comap (complement I).ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (x.val ∈ I.support ↔ False)
  exact iff_false_intro x.property

/-- Every power inclusion is invertible on the complement of the original ideal. -/
theorem power_inclusion_complement [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsFinitePresentation] :
    IsIso ((restrictFunctor (complement I).ι).map (inclusion (I ^ n) F)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (complement I).ι
  have := coherentPresentation_restrict (complement I).ι F
  rw [← powerRestrictIso_comp I n F (complement I).ι]
  have h : IsIso (inclusion ((I.comap (complement I).ι) ^ n)
      (F.restrict (complement I).ι)) := by
    rw [comap_complement, show (⊤ : (complement I).toScheme.IdealSheafData) ^ n = ⊤ from
      (one_pow n : (1 : (complement I).toScheme.IdealSheafData) ^ n = 1)]
    infer_instance
  infer_instance

/-- Restriction carries a power transition to the transition for the pulled-back ideal. -/
lemma transition_restrict [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] {a b : ℕ} (h : a ≤ b) (j : Y ⟶ X) [IsOpenImmersion j] :
    have := LocallyOfFiniteType.isLocallyNoetherian j
    have := coherentPresentation_restrict j F
    (restrictFunctor j).map (transition I F h) ≫ (powerRestrictIso I a F j).hom =
      (powerRestrictIso I b F j).hom ≫ transition (I.comap j) (F.restrict j) h := by
  have := LocallyOfFiniteType.isLocallyNoetherian j
  have := coherentPresentation_restrict j F
  apply (cancel_mono (inclusion ((I.comap j) ^ a) (F.restrict j))).mp
  rw [Category.assoc, powerRestrictIso_comp, ← Functor.map_comp, transition_comp,
    Category.assoc, transition_comp, powerRestrictIso_comp]

/-- Higher-to-lower transitions compose without choices. -/
lemma transition_trans [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsFinitePresentation] {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    transition I F hbc ≫ transition I F hab = transition I F (hab.trans hbc) := by
  apply (cancel_mono (inclusion (I ^ a) F)).mp
  simp

/-- In an affine chart the transported coordinate ideal is exactly the original affine ideal. -/
lemma specIdeal_fromSpec (I : X.IdealSheafData) (V : X.affineOpens) :
    specIdeal (I.comap V.2.fromSpec) = I.ideal V := by
  let h : (⊤ : (Spec Γ(X, V.1)).Opens) ≤ V.2.fromSpec ⁻¹ᵁ V.1 := by
    rw [V.2.fromSpec_preimage_self]
  have he : V.2.fromSpec.appLE V.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, V.1)).inv := by
    rw [Scheme.Hom.appLE, V.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have hh : (eqToHom V.2.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hh, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [specIdeal, Scheme.IdealSheafData.ideal_comap I V.2.fromSpec V
    ⟨⊤, isAffineOpen_top _⟩ h, he, Ideal.map_map, ← CommRingCat.hom_comp]
  simp

end FLT.Mazur.GlobalIdealPowerCompatibility
