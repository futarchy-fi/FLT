/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicDedekind

/-! # The finite étale cyclic incidence family

Over a Dedekind coefficient base, adjoin the zero section to the generator
scheme over the scalar quotient. The resulting family embeds as an open
and closed subscheme of the torsion scheme over the quotient. Its group
structure and prime-level degree are established separately.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

/-- Disjoint open subschemes embed by their coproduct. -/
theorem coprodDesc_open_of_disjoint {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : Disjoint (Set.range f) (Set.range g)) :
    IsOpenImmersion (coprod.desc f g) := by
  apply IsOpenImmersion.of_openCover_source _ (coprodOpenCover.{u, 0} X Y)
  · intro x y he
    obtain ⟨x, rfl⟩ := (coprodMk X Y).surjective x
    obtain ⟨y, rfl⟩ := (coprodMk X Y).surjective y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc] at he
        exact congrArg (fun z => coprodMk X Y (Sum.inl z)) (f.injective he)
      | inr y =>
        simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
          coprod.inl_desc, coprod.inr_desc] at he
        exact (Set.disjoint_iff_forall_ne.mp h ⟨x, rfl⟩ ⟨y, rfl⟩ he).elim
    | inr x =>
      cases y with
      | inl y =>
        simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
          coprod.inl_desc, coprod.inr_desc] at he
        exact (Set.disjoint_iff_forall_ne.mp h ⟨y, rfl⟩ ⟨x, rfl⟩ he.symm).elim
      | inr y =>
        simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc] at he
        exact congrArg (fun z => coprodMk X Y (Sum.inr z)) (g.injective he)
  · rintro (i | i) <;>
      simp only [coprodOpenCover, 
        coprod.inl_desc, coprod.inr_desc] <;> infer_instance

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- The torsion scheme pulled back to the scalar parameter space. -/
def cyclicIncidenceAmbient : Scheme :=
  pullback (scalarQuotientModel W n).hom (torsionModel W n).hom

/-- The zero section of the torsion scheme over cyclic parameters. -/
def cyclicIncidenceZero : (scalarQuotientModel W n).left ⟶ cyclicIncidenceAmbient W n :=
  pullback.lift (𝟙 _) ((scalarQuotientModel W n).hom ≫ torsionZeroSection W n) (by simp)

/-- The incidence map sending a generator to its scalar orbit and torsion point. -/
def cyclicIncidenceGenerator : (nonzeroTorsionModel W n).left ⟶
    cyclicIncidenceAmbient W n :=
  pullback.lift (scalarQuotientMap W n).left (nonzeroTorsionInclusion W n).left
    ((scalarQuotientMap W n).w.trans (nonzeroTorsionInclusion W n).w.symm)

/-- The zero part of the incidence family is open. -/
theorem cyclicIncidenceZero_open : IsOpenImmersion (cyclicIncidenceZero W n) := by
  have := torsionModel_etale W n Fact.out
  have : Etale (cyclicIncidenceZero W n ≫
      pullback.fst (scalarQuotientModel W n).hom (torsionModel W n).hom) := by
    simp only [cyclicIncidenceZero, pullback.lift_fst]
    infer_instance
  have : Mono (cyclicIncidenceZero W n) :=
    mono_of_mono_fac (show cyclicIncidenceZero W n ≫
      pullback.fst _ _ = 𝟙 _ from pullback.lift_fst _ _ _)
  have := Etale.of_comp (cyclicIncidenceZero W n) (pullback.fst _ _)
  exact IsOpenImmersion.of_flat_of_mono _

/-- The generator part of the incidence family is open over a Dedekind base. -/
theorem cyclicIncidenceGenerator_open :
    IsOpenImmersion (cyclicIncidenceGenerator W n) := by
  have := scalarQuotientModel_etale_dedekind W n
  have : Etale (cyclicIncidenceGenerator W n ≫
      pullback.snd (scalarQuotientModel W n).hom (torsionModel W n).hom) := by
    simp only [cyclicIncidenceGenerator, pullback.lift_snd]
    change Etale (nonzeroTorsionOpen W n).ι
    infer_instance
  have : Mono (cyclicIncidenceGenerator W n) :=
    mono_of_mono_fac (show cyclicIncidenceGenerator W n ≫
      pullback.snd _ _ = (nonzeroTorsionOpen W n).ι from pullback.lift_snd _ _ _)
  have := Etale.of_comp (cyclicIncidenceGenerator W n) (pullback.snd _ _)
  exact IsOpenImmersion.of_flat_of_mono _

/-- The zero part and the generator part have disjoint images. -/
theorem cyclicIncidence_disjoint :
    Disjoint (Set.range (cyclicIncidenceZero W n))
      (Set.range (cyclicIncidenceGenerator W n)) := by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have h' := congrArg (pullback.snd (scalarQuotientModel W n).hom
    (torsionModel W n).hom) h
  change ((cyclicIncidenceZero W n ≫ pullback.snd _ _) x) =
    ((cyclicIncidenceGenerator W n ≫ pullback.snd _ _) y) at h'
  simp only [cyclicIncidenceZero, cyclicIncidenceGenerator, pullback.lift_snd] at h'
  exact y.property ⟨(scalarQuotientModel W n).hom x, h'⟩

/-- The incidence family, consisting of zero and the nonzero generators. -/
def cyclicIncidenceFamily : Scheme :=
  (scalarQuotientModel W n).left ⨿ (nonzeroTorsionModel W n).left

/-- The incidence family maps to the cyclic parameter space. -/
def cyclicIncidenceToBase : cyclicIncidenceFamily W n ⟶ (scalarQuotientModel W n).left :=
  coprod.desc (𝟙 _) (scalarQuotientMap W n).left

/-- The incidence family embeds into the torsion scheme over the parameters. -/
def cyclicIncidenceInclusion : cyclicIncidenceFamily W n ⟶ cyclicIncidenceAmbient W n :=
  coprod.desc (cyclicIncidenceZero W n) (cyclicIncidenceGenerator W n)

/-- The incidence family is an open subscheme of the ambient torsion scheme. -/
theorem cyclicIncidenceInclusion_open :
    IsOpenImmersion (cyclicIncidenceInclusion W n) := by
  have := cyclicIncidenceZero_open W n
  have := cyclicIncidenceGenerator_open W n
  exact coprodDesc_open_of_disjoint _ _ (cyclicIncidence_disjoint W n)

/-- The incidence family is finite over its cyclic parameters. -/
theorem cyclicIncidenceToBase_finite : IsFinite (cyclicIncidenceToBase W n) := by
  have := scalarQuotientMap_finite W n
  exact inferInstanceAs (IsFinite (coprod.desc (𝟙 _) (scalarQuotientMap W n).left))

/-- The incidence embedding respects the parameter projection. -/
theorem cyclicIncidenceInclusion_toBase :
    cyclicIncidenceInclusion W n ≫
      pullback.fst (scalarQuotientModel W n).hom (torsionModel W n).hom =
      cyclicIncidenceToBase W n := by
  apply coprod.hom_ext <;> simp [cyclicIncidenceInclusion,
    cyclicIncidenceToBase, cyclicIncidenceZero, cyclicIncidenceGenerator]

/-- The incidence family is étale over its cyclic parameters. -/
theorem cyclicIncidenceToBase_etale : Etale (cyclicIncidenceToBase W n) := by
  have := cyclicIncidenceInclusion_open W n
  have := torsionModel_etale W n Fact.out
  rw [← cyclicIncidenceInclusion_toBase]
  infer_instance

/-- The incidence family is also a closed subscheme of the ambient torsion scheme. -/
theorem cyclicIncidenceInclusion_closed :
    IsClosedImmersion (cyclicIncidenceInclusion W n) := by
  have := cyclicIncidenceToBase_finite W n
  have := cyclicIncidenceInclusion_open W n
  have : IsFinite (cyclicIncidenceInclusion W n ≫
      pullback.fst (scalarQuotientModel W n).hom (torsionModel W n).hom) := by
    rw [cyclicIncidenceInclusion_toBase]
    infer_instance
  have := IsFinite.of_comp (cyclicIncidenceInclusion W n) (pullback.fst _ _)
  apply IsClosedImmersion.of_isPreimmersion
  exact (cyclicIncidenceInclusion W n).isClosedMap.isClosed_range

end WeierstrassCurve.CubicCharts
