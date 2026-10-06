/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicDedekind
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
/-! # Integral extension and specialization of cyclic parameters

A parameter over the fraction field of a normal coefficient ring extends
uniquely to an integral section. This defines specialization to a residue
field. Over a local Dedekind base, the scalar quotient is étale, so two
sections agreeing on the residue field coincide; specialization is injective.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
/-- Sections of an unramified finite-type morphism over a local ring agree if reductions do. -/
theorem unramifiedSection_residue_injective
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of R)) [FormallyUnramified s] [LocallyOfFiniteType s]
    (f g : Spec (.of R) ⟶ X) (hf : f ≫ s = 𝟙 _) (hg : g ≫ s = 𝟙 _)
    (hred : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ f =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ g) : f = g := by
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let pair := pullback.lift f g (hf.trans hg.symm)
  let d := pullback.diagonal s
  let j := pullback.snd d pair
  have : IsOpenImmersion j := inferInstance
  have he : (r ≫ f) ≫ d = r ≫ pair := by
    apply pullback.hom_ext <;> simp only [Category.assoc, d, pair,
      pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id]
    exact hred
  let e := pullback.lift (r ≫ f) r he
  have hclosed : IsLocalRing.closedPoint R ∈ Set.range j := by
    refine ⟨e (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)), ?_⟩
    change (e ≫ j) _ = _
    rw [pullback.lift_snd]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have : Surjective j := ⟨fun x =>
    (IsLocalRing.specializes_closedPoint x).mem_open
      j.isOpenEmbedding.isOpen_range hclosed⟩
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr
    ⟨inferInstance, inferInstance⟩
  apply (cancel_epi j).mp
  have h₁ := congrArg (fun a => a ≫ pullback.fst s s) (pullback.condition (f := d) (g := pair))
  have h₂ := congrArg (fun a => a ≫ pullback.snd s s) (pullback.condition (f := d) (g := pair))
  simp only [Category.assoc, d, pair, pullback.diagonal_fst, pullback.diagonal_snd,
    pullback.lift_fst, pullback.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.symm.trans h₂

section Integral
variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- A point of a finite algebra over a normal ring extends from its fraction field. -/
theorem integralAlgPoint_extension (A : Type u) [CommRing A] [Algebra R A]
    [Module.Finite R A] (f : A →ₐ[R] K) :
    ∃ g : A →ₐ[R] R, (Algebra.ofId R K).comp g = f := by
  let i := Algebra.ofId R K
  let e := AlgEquiv.ofInjective i (IsFractionRing.injective R K)
  have hr : ∀ a, f a ∈ i.range := by
    intro a
    exact IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral a).map f)
  let h := f.codRestrict i.range hr
  refine ⟨e.symm.toAlgHom.comp h, ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (h a))

variable [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- A fraction-field scalar parameter extends uniquely to an integral section. -/
theorem scalarQuotientPoint_integral_extension
    (q : pointSource K ⟶ scalarQuotientModel W n) :
    ∃! s : pointSource R ⟶ scalarQuotientModel W n,
      pointSourceMap (Algebra.ofId R K) ≫ s = q := by
  let D := TorsionScalarInvariantRing W n
  have := torsionScalarInvariantRing_finite W n
  let eR : (D →ₐ[R] R) ≃ (pointSource R ⟶ scalarQuotientModel W n) :=
    specAlgPointEquiv D R
  let eK := scalarQuotientCoordinatePointEquiv (K := K) W n
  have hmap (g : D →ₐ[R] R) :
      pointSourceMap (Algebra.ofId R K) ≫ eR g = eK ((Algebra.ofId R K).comp g) := by
    apply Over.OverMorphism.ext
    exact (Spec.map_comp (CommRingCat.ofHom g.toRingHom)
      (CommRingCat.ofHom (algebraMap R K))).symm
  obtain ⟨f, rfl⟩ := eK.surjective q
  obtain ⟨g, hg⟩ := integralAlgPoint_extension K D f
  refine ⟨eR g, ?_, ?_⟩
  · dsimp only
    rw [hmap, hg]
  · intro s hs
    obtain ⟨g', rfl⟩ := eR.surjective s
    rw [hmap] at hs
    apply congrArg eR
    ext a
    apply IsFractionRing.injective R K
    exact AlgHom.congr_fun ((eK.injective hs).trans hg.symm) a


/-- The unique integral section extending a fraction-field scalar parameter. -/
def scalarQuotientIntegralSection
    (q : pointSource K ⟶ scalarQuotientModel W n) :
    pointSource R ⟶ scalarQuotientModel W n :=
  (scalarQuotientPoint_integral_extension K W n q).choose

/-- The integral extension restricts to the original fraction-field parameter. -/
theorem scalarQuotientIntegralSection_restrict
    (q : pointSource K ⟶ scalarQuotientModel W n) :
    pointSourceMap (Algebra.ofId R K) ≫ scalarQuotientIntegralSection K W n q = q :=
  (scalarQuotientPoint_integral_extension K W n q).choose_spec.1

/-- Any integral extension equals the canonical section. -/
theorem scalarQuotientIntegralSection_unique
    (q : pointSource K ⟶ scalarQuotientModel W n)
    (s : pointSource R ⟶ scalarQuotientModel W n)
    (hs : pointSourceMap (Algebra.ofId R K) ≫ s = q) :
    s = scalarQuotientIntegralSection K W n q :=
  (scalarQuotientPoint_integral_extension K W n q).choose_spec.2 s hs

/-- Specialize a fraction-field parameter using its unique integral extension. -/
def scalarQuotientSpecialization (k : Type u) [Field k] [Algebra R k]
    (q : pointSource K ⟶ scalarQuotientModel W n) :
    pointSource k ⟶ scalarQuotientModel W n :=
  pointSourceMap (Algebra.ofId R k) ≫ scalarQuotientIntegralSection K W n q

/-- Specialization of an integral section is its ordinary restriction to the residue field. -/
theorem scalarQuotientSpecialization_of_section
    (k : Type u) [Field k] [Algebra R k]
    (s : pointSource R ⟶ scalarQuotientModel W n) :
    scalarQuotientSpecialization K W n k (pointSourceMap (Algebra.ofId R K) ≫ s) =
      pointSourceMap (Algebra.ofId R k) ≫ s := by
  unfold scalarQuotientSpecialization
  rw [← scalarQuotientIntegralSection_unique K W n _ s rfl]


end Integral

variable {R : Type u} [CommRing R] [IsDedekindDomain R] [IsLocalRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- Scalar parameter specialization is injective over a local Dedekind base. -/
theorem scalarQuotientSpecialization_injective :
    Function.Injective (scalarQuotientSpecialization K W n (IsLocalRing.ResidueField R)) := by
  intro x y h
  have := scalarQuotientModel_etale_dedekind W n
  have he : scalarQuotientIntegralSection K W n x = scalarQuotientIntegralSection K W n y := by
    apply Over.OverMorphism.ext
    apply unramifiedSection_residue_injective (scalarQuotientModel W n).hom
    · simp
    · simp
    · exact congrArg Over.Hom.left h
  rw [← scalarQuotientIntegralSection_restrict K W n x,
    ← scalarQuotientIntegralSection_restrict K W n y, he]

end WeierstrassCurve.CubicCharts
