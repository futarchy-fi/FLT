/-
Copyright (c) 2025 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.LiftFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The de Smit–Lenstra criterion for corepresentability of deformation functors

This file develops the general machinery used in the proof of
de Smit–Lenstra, *Explicit construction of universal deformation rings*
(in *Modular Forms and Fermat's Last Theorem*, Springer 1997), Proposition 2.3, that the
deformation functor of an absolutely irreducible residual representation is corepresentable.

## Main definitions

* `CategoryTheory.Functor.IsUniversalElement`: `u : F.obj R` is a *universal element* of a
  type-valued functor `F` when every element of `F.obj S` is `F.map f u` for a unique
  `f : R ⟶ S`. This is the elementwise form of corepresentability.
* `CategoryTheory.Functor.IsPullbackSurjective`,
  `CategoryTheory.Functor.IsPullbackInjective`: the two halves of the Schlessinger comparison
  map `F (A ×_Q B) → F A ×_(F Q) F B`, stated for an arbitrary pullback square.
* `Deformation.IsUniversalLift`: a lift `σ` of `ρ` to `R` such that every lift of `ρ` to any `S`
  is, up to conjugation by an element of `ker(GLₙ(S) → GLₙ(𝕜))`, the pushforward of `σ` along a
  unique morphism `R ⟶ S`.

## Main results

* `CategoryTheory.Functor.corepresentableByOfIsUniversalElement`,
  `CategoryTheory.Functor.isCorepresentable_of_isUniversalElement`: a functor with a
  universal element is corepresentable, and conversely
  (`CategoryTheory.Functor.isUniversalElement_homEquiv_id`).
* `Deformation.toRepnQuot_app_residueField_injective`: over the residue field the relation of
  conjugation by the kernel of `GLₙ(R) → GLₙ(𝕜)` is trivial, so `repnQuotFunctor` and
  `repnFunctor` agree there.
* `Deformation.mem_deformationFunctor_iff`: a class of representations lies in the deformation
  functor exactly when any (equivalently, some) representative is a lift of `ρ`; hence
  `Deformation.deformationFunctor_obj_eq_image`: the deformation functor is the image of the
  lift functor.
* `Deformation.isCorepresentable_deformationFunctor_of_universalLift`: the reduction of
  corepresentability of the deformation functor to the existence of a universal lift, i.e. of a
  lift `σ` of `ρ` to some `R` such that every lift of `ρ` to any `S` is, up to conjugation by an
  element of `ker(GLₙ(S) → GLₙ(𝕜))`, obtained from `σ` along a *unique* morphism `R ⟶ S`.
  This is the statement that de Smit and Lenstra's explicit construction is designed to verify;
  `Deformation.isCorepresentable_deformationFunctor_iff_exists_isUniversalLift` records that the
  reduction is in fact an equivalence.
* `CategoryTheory.Functor.CorepresentableBy.isPullbackSurjective`,
  `CategoryTheory.Functor.CorepresentableBy.isPullbackInjective`: the *necessity* half of
  Schlessinger's criterion — a corepresentable functor turns every pullback square into a
  pullback square of sets.

## What is not proved here

The existence of a universal lift for an absolutely irreducible `ρ` over a profinite group
(de Smit–Lenstra, Proposition 2.3 (1)) is *not* proved: that requires their explicit
construction, via the completed group algebra `𝓞[[G]]`, Burnside surjectivity onto `Mₙ(𝕜)`,
lifting of matrix units, and the resulting Morita identification `𝓞[[G]]^ ≅ Mₙ(Rᵘⁿⁱᵛ)`.
Consequently `FLT.Deformations.Representable.isCorepresentable_deformationFunctor` is left
unproved; what this file supplies is the complete, unconditional reduction around it.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe w v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- An element `u : F.obj R` is a *universal element* of the type-valued functor `F` if for
every object `S` and every `x : F.obj S` there is a unique morphism `f : R ⟶ S` with
`F.map f u = x`. Equivalently, `⟨R, u⟩` is an initial object of the category of elements of
`F`. -/
def IsUniversalElement {R : C} (u : F.obj R) : Prop :=
  ∀ (S : C) (x : F.obj S), ∃! f : R ⟶ S, F.map f u = x

namespace IsUniversalElement

variable {F} {R : C} {u : F.obj R}

/-- The morphism produced by a universal element. -/
noncomputable def desc (hu : F.IsUniversalElement u) (S : C) (x : F.obj S) : R ⟶ S :=
  (hu S x).choose

@[simp]
lemma map_desc (hu : F.IsUniversalElement u) (S : C) (x : F.obj S) :
    F.map (hu.desc S x) u = x :=
  (hu S x).choose_spec.1

lemma desc_unique (hu : F.IsUniversalElement u) {S : C} {x : F.obj S} {f : R ⟶ S}
    (hf : F.map f u = x) : f = hu.desc S x :=
  (hu S x).choose_spec.2 f hf

lemma eq_of_map_eq (hu : F.IsUniversalElement u) {S : C} {f g : R ⟶ S}
    (h : F.map f u = F.map g u) : f = g :=
  (hu.desc_unique h).trans (hu.desc_unique rfl).symm

end IsUniversalElement

/-- A functor with a universal element is corepresented by the object carrying it. -/
noncomputable def corepresentableByOfIsUniversalElement {R : C} {u : F.obj R}
    (hu : F.IsUniversalElement u) : F.CorepresentableBy R where
  homEquiv {S} :=
    { toFun f := F.map f u
      invFun x := hu.desc S x
      left_inv f := (hu.desc_unique rfl).symm
      right_inv x := hu.map_desc S x }
  homEquiv_comp {S S'} g f := by simp

lemma isCorepresentable_of_isUniversalElement {R : C} {u : F.obj R}
    (hu : F.IsUniversalElement u) : F.IsCorepresentable :=
  (F.corepresentableByOfIsUniversalElement hu).isCorepresentable

/-- Conversely, a corepresentation of `F` by `R` exhibits the image of the identity as a
universal element. -/
lemma isUniversalElement_homEquiv_id {R : C} (e : F.CorepresentableBy R) :
    F.IsUniversalElement (e.homEquiv (𝟙 R)) := by
  intro S x
  refine ⟨e.homEquiv.symm x, ?_, ?_⟩
  · dsimp only
    rw [← CorepresentableBy.homEquiv_eq, Equiv.apply_symm_apply]
  · intro f hf
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply, e.homEquiv_eq]
    exact hf


/-!
## Schlessinger-style conditions

Schlessinger's criterion for (pro-)representability of a deformation functor is expressed in
terms of the comparison map `F (A ×_Q B) → F A ×_{F Q} F B` attached to a fibre product of
coefficient rings. The two halves of that comparison — surjectivity (the shape of
Schlessinger's `H1` and `H2`) and injectivity (the shape of the extra rigidity supplied by `H4`
in the absolutely irreducible case) — are recorded here for an arbitrary pullback square.

Only the *necessity* of these conditions is proved below: a corepresentable functor satisfies
them for **every** pullback square, because `Hom(X, -)` preserves limits. Schlessinger's theorem
is the converse, for squares whose right-hand map is a small surjection; that converse is not
proved here.
-/

/-- `F` is *pullback surjective* if for every pullback square in `C` the comparison map
`F.obj P → F.obj A ×_(F.obj Q) F.obj B` is surjective. This is the shape of Schlessinger's
conditions `H1` and `H2`, which only require it for squares whose right-hand map is a small
surjection. -/
def IsPullbackSurjective : Prop :=
  ∀ ⦃P A B Q : C⦄ (fst : P ⟶ A) (snd : P ⟶ B) (f : A ⟶ Q) (g : B ⟶ Q),
    IsPullback fst snd f g → ∀ (a : F.obj A) (b : F.obj B), F.map f a = F.map g b →
      ∃ p : F.obj P, F.map fst p = a ∧ F.map snd p = b

/-- `F` is *pullback injective* if for every pullback square in `C` the comparison map
`F.obj P → F.obj A ×_(F.obj Q) F.obj B` is injective. Together with `IsPullbackSurjective` this
says that `F` turns pullback squares into pullback squares of sets; it is the shape of the
rigidity that Schlessinger's `H4` provides for absolutely irreducible residual
representations. -/
def IsPullbackInjective : Prop :=
  ∀ ⦃P A B Q : C⦄ (fst : P ⟶ A) (snd : P ⟶ B) (f : A ⟶ Q) (g : B ⟶ Q),
    IsPullback fst snd f g → ∀ p p' : F.obj P,
      F.map fst p = F.map fst p' → F.map snd p = F.map snd p' → p = p'

variable {F}

/-- A corepresentable functor is pullback surjective: this is the existence half of the
universal property of a pullback, transported along the corepresentation. -/
theorem CorepresentableBy.isPullbackSurjective {X : C} (e : F.CorepresentableBy X) :
    F.IsPullbackSurjective := by
  intro P A B Q fst snd f g hP a b hab
  obtain ⟨α, rfl⟩ := e.homEquiv.surjective a
  obtain ⟨β, rfl⟩ := e.homEquiv.surjective b
  rw [← e.homEquiv_comp, ← e.homEquiv_comp] at hab
  have hαβ : α ≫ f = β ≫ g := e.homEquiv.injective hab
  refine ⟨e.homEquiv (hP.lift α β hαβ), ?_, ?_⟩
  · rw [← e.homEquiv_comp, hP.lift_fst]
  · rw [← e.homEquiv_comp, hP.lift_snd]

/-- A corepresentable functor is pullback injective: this is the uniqueness half of the
universal property of a pullback, transported along the corepresentation. -/
theorem CorepresentableBy.isPullbackInjective {X : C} (e : F.CorepresentableBy X) :
    F.IsPullbackInjective := by
  intro P A B Q fst snd f g hP p p' hfst hsnd
  obtain ⟨π, rfl⟩ := e.homEquiv.surjective p
  obtain ⟨π', rfl⟩ := e.homEquiv.surjective p'
  rw [← e.homEquiv_comp, ← e.homEquiv_comp] at hfst hsnd
  exact congrArg _ (hP.hom_ext (e.homEquiv.injective hfst) (e.homEquiv.injective hsnd))

theorem isPullbackSurjective_of_isCorepresentable [F.IsCorepresentable] :
    F.IsPullbackSurjective :=
  (F.corepresentableBy).isPullbackSurjective

theorem isPullbackInjective_of_isCorepresentable [F.IsCorepresentable] :
    F.IsPullbackInjective :=
  (F.corepresentableBy).isPullbackInjective

end CategoryTheory.Functor

namespace Deformation

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

section Quot

variable (n G 𝓞)

/-- Two continuous representations define the same element of `repnQuotFunctor` exactly when
they are conjugate by an element of the kernel of the reduction map `GLₙ(R) → GLₙ(𝕜)`. -/
lemma repnQuot_mk_eq_iff {R : ProartinianCat 𝓞} (x y : (repnFunctor n G 𝓞).obj R) :
    (toRepnQuot n G 𝓞).app R x = (toRepnQuot n G 𝓞).app R y ↔
      ∃ γ : GL n R, Matrix.GeneralLinearGroup.map (ProartinianCat.toResidueField R).hom.toRingHom
          γ = 1 ∧ ∀ g : G, DFunLike.coe (F := G →ₜ* GL n R) x g =
            γ * DFunLike.coe (F := G →ₜ* GL n R) y g * γ⁻¹ := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := Quotient.eq''.mp h
    refine ⟨ConjAct.ofConjAct γ.1, γ.2, fun g ↦ ?_⟩
    exact congrArg (fun z : G →ₜ* GL n R ↦ z g) hγ.symm
  · rintro ⟨γ, hγ, hxy⟩
    refine Quotient.eq''.mpr ⟨⟨ConjAct.toConjAct γ, hγ⟩, ?_⟩
    exact DFunLike.ext (F := G →ₜ* GL n R) _ _ fun g ↦ (hxy g).symm

/-- Over the residue field the group we quotient by is trivial, so passing to the quotient
functor loses no information. -/
lemma toRepnQuot_app_residueField_injective :
    Function.Injective ((toRepnQuot n G 𝓞).app (.residueField)) := by
  intro x y h
  obtain ⟨γ, hγ, hxy⟩ := (repnQuot_mk_eq_iff n G 𝓞 x y).mp h
  have hid : (ProartinianCat.toResidueField
      (ProartinianCat.residueField (𝓞 := 𝓞))).hom.toRingHom =
      RingHom.id (ProartinianCat.residueField (𝓞 := 𝓞)) := by
    rw [Subsingleton.elim (ProartinianCat.toResidueField
      (ProartinianCat.residueField (𝓞 := 𝓞))) (𝟙 _)]
    rfl
  rw [hid, Matrix.GeneralLinearGroup.map_id] at hγ
  have hγ1 : γ = 1 := by simpa using hγ
  refine DFunLike.ext (F := G →ₜ* GL n (ProartinianCat.residueField (𝓞 := 𝓞))) x y fun g ↦ ?_
  rw [hxy g, hγ1, one_mul, inv_one, mul_one]

end Quot

section Deformations

variable (n G 𝓞) (ρ : (repnFunctor n G 𝓞).obj .residueField)

lemma mem_liftFunctor_iff {R : ProartinianCat 𝓞} (x : (repnFunctor n G 𝓞).obj R) :
    x ∈ (liftFunctor n G 𝓞 ρ).obj R ↔
      (repnFunctor n G 𝓞).map (ProartinianCat.toResidueField R) x = ρ := by
  change (repnFunctor n G 𝓞).map
    (ProartinianCat.isTerminalResidueField.from R) x ∈ ({ρ} : Set _) ↔ _
  rw [Subsingleton.elim (ProartinianCat.isTerminalResidueField.from R)
    (ProartinianCat.toResidueField R)]
  exact Set.mem_singleton_iff

/-- A class of continuous representations is a deformation of `ρ` exactly when one (equivalently
any) of its representatives is a lift of `ρ`. This identifies the deformation functor with the
quotient of the lift functor. -/
lemma mem_deformationFunctor_iff {R : ProartinianCat 𝓞} (x : (repnFunctor n G 𝓞).obj R) :
    (toRepnQuot n G 𝓞).app R x ∈ (deformationFunctor n G 𝓞 ρ).obj R ↔
      x ∈ (liftFunctor n G 𝓞 ρ).obj R := by
  change (repnQuotFunctor n G 𝓞).map (ProartinianCat.isTerminalResidueField.from R)
    ((toRepnQuot n G 𝓞).app R x) ∈ ({_} : Set _) ↔ _
  rw [Set.mem_singleton_iff,
    show (repnQuotFunctor n G 𝓞).map (ProartinianCat.isTerminalResidueField.from R)
      ((toRepnQuot n G 𝓞).app R x) =
      (toRepnQuot n G 𝓞).app _ ((repnFunctor n G 𝓞).map
        (ProartinianCat.isTerminalResidueField.from R) x) from rfl]
  rw [(toRepnQuot_app_residueField_injective n G 𝓞).eq_iff, mem_liftFunctor_iff]
  rw [Subsingleton.elim (ProartinianCat.isTerminalResidueField.from R)
    (ProartinianCat.toResidueField R)]

lemma toRepnQuot_app_surjective (R : ProartinianCat 𝓞) :
    Function.Surjective ((toRepnQuot n G 𝓞).app R) :=
  Quotient.mk''_surjective

/-- The deformation functor is exactly the image of the lift functor under the quotient map. -/
lemma deformationFunctor_obj_eq_image (R : ProartinianCat 𝓞) :
    (deformationFunctor n G 𝓞 ρ).obj R =
      (toRepnQuot n G 𝓞).app R '' ((liftFunctor n G 𝓞 ρ).obj R) := by
  ext q
  obtain ⟨x, rfl⟩ := toRepnQuot_app_surjective n G 𝓞 R q
  rw [mem_deformationFunctor_iff]
  refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, hxy⟩
  exact (mem_deformationFunctor_iff n G 𝓞 ρ x).mp
    (hxy ▸ (mem_deformationFunctor_iff n G 𝓞 ρ y).mpr hy)

/-- **The de Smit–Lenstra reduction.** To corepresent the deformation functor of `ρ` it suffices
to produce a *universal lift*: a lift `σ` of `ρ` to some object `R` of `ProartinianCat 𝓞` such
that for every object `S` and every lift `τ` of `ρ` to `S`, there is a *unique* morphism
`f : R ⟶ S` carrying `σ` to a representation conjugate to `τ` by an element of
`ker(GLₙ(S) → GLₙ(𝕜))`.

This isolates the general nonsense; what de Smit and Lenstra supply (for `ρ` absolutely
irreducible over a profinite group) is the universal lift itself. -/
theorem isCorepresentable_deformationFunctor_of_universalLift
    (R : ProartinianCat 𝓞) (σ : (repnFunctor n G 𝓞).obj R)
    (hσ : σ ∈ (liftFunctor n G 𝓞 ρ).obj R)
    (huniv : ∀ (S : ProartinianCat 𝓞) (τ : (repnFunctor n G 𝓞).obj S),
      τ ∈ (liftFunctor n G 𝓞 ρ).obj S →
        ∃! f : R ⟶ S, (toRepnQuot n G 𝓞).app S ((repnFunctor n G 𝓞).map f σ) =
          (toRepnQuot n G 𝓞).app S τ) :
    (deformationFunctor n G 𝓞 ρ).toFunctor.IsCorepresentable := by
  refine Functor.isCorepresentable_of_isUniversalElement _
    (u := (⟨(toRepnQuot n G 𝓞).app R σ,
      (mem_deformationFunctor_iff n G 𝓞 ρ σ).mpr hσ⟩ :
        (deformationFunctor n G 𝓞 ρ).toFunctor.obj R)) ?_
  intro S x
  obtain ⟨τ, hτx⟩ := toRepnQuot_app_surjective n G 𝓞 S x.1
  have hτ : τ ∈ (liftFunctor n G 𝓞 ρ).obj S :=
    (mem_deformationFunctor_iff n G 𝓞 ρ τ).mp (by rw [hτx]; exact x.2)
  obtain ⟨f, hf, hf'⟩ := huniv S τ hτ
  refine ⟨f, Subtype.ext (hf.trans hτx), fun g hg ↦ hf' g ?_⟩
  exact (congrArg Subtype.val hg).trans hτx.symm


/-- The natural transformation sending a lift of `ρ` to the deformation it represents. -/
@[simps]
noncomputable def liftToDeformation :
    (liftFunctor n G 𝓞 ρ).toFunctor ⟶ (deformationFunctor n G 𝓞 ρ).toFunctor where
  app R := ↾fun x ↦ ⟨(toRepnQuot n G 𝓞).app R x.1,
    (mem_deformationFunctor_iff n G 𝓞 ρ x.1).mpr x.2⟩
  naturality _ _ _ := rfl

/-- Every deformation of `ρ` comes from a lift of `ρ`. -/
lemma liftToDeformation_app_surjective (R : ProartinianCat 𝓞) :
    Function.Surjective ((liftToDeformation n G 𝓞 ρ).app R) := by
  rintro ⟨q, hq⟩
  rw [deformationFunctor_obj_eq_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨⟨x, hx⟩, rfl⟩

/-- A *universal lift* of `ρ`: a lift `σ` of `ρ` to `R` such that every lift of `ρ` to any `S`
is, up to conjugation by an element of `ker(GLₙ(S) → GLₙ(𝕜))`, the pushforward of `σ` along a
unique morphism `R ⟶ S`. -/
def IsUniversalLift {R : ProartinianCat 𝓞} (σ : (repnFunctor n G 𝓞).obj R) : Prop :=
  σ ∈ (liftFunctor n G 𝓞 ρ).obj R ∧
    ∀ (S : ProartinianCat 𝓞) (τ : (repnFunctor n G 𝓞).obj S),
      τ ∈ (liftFunctor n G 𝓞 ρ).obj S →
        ∃! f : R ⟶ S, (toRepnQuot n G 𝓞).app S ((repnFunctor n G 𝓞).map f σ) =
          (toRepnQuot n G 𝓞).app S τ

/-- **The de Smit–Lenstra reduction.** The deformation functor of `ρ` is corepresentable if and
only if `ρ` has a universal lift. The substance of de Smit–Lenstra, Proposition 2.3 (1), is the
construction of such a universal lift when `ρ` is absolutely irreducible and `G` is profinite;
everything else is the general nonsense recorded here. -/
theorem isCorepresentable_deformationFunctor_iff_exists_isUniversalLift :
    (deformationFunctor n G 𝓞 ρ).toFunctor.IsCorepresentable ↔
      ∃ (R : ProartinianCat 𝓞) (σ : (repnFunctor n G 𝓞).obj R),
        IsUniversalLift n G 𝓞 ρ σ := by
  constructor
  · intro h
    obtain ⟨R, ⟨e⟩⟩ := h.has_corepresentation
    have hu := Functor.isUniversalElement_homEquiv_id _ e
    set u := e.homEquiv (𝟙 R) with hu_def
    obtain ⟨σ, hσq⟩ := toRepnQuot_app_surjective n G 𝓞 R u.1
    have hσ : σ ∈ (liftFunctor n G 𝓞 ρ).obj R :=
      (mem_deformationFunctor_iff n G 𝓞 ρ σ).mp (by rw [hσq]; exact u.2)
    refine ⟨R, σ, hσ, fun S τ hτ ↦ ?_⟩
    obtain ⟨f, hf, hf'⟩ := hu S ⟨(toRepnQuot n G 𝓞).app S τ,
      (mem_deformationFunctor_iff n G 𝓞 ρ τ).mpr hτ⟩
    refine ⟨f, ?_, fun g hg ↦ hf' g (Subtype.ext ?_)⟩
    · have := congrArg Subtype.val hf
      rwa [show ((deformationFunctor n G 𝓞 ρ).toFunctor.map f u).1 =
        (repnQuotFunctor n G 𝓞).map f u.1 from rfl, ← hσq] at this
    · rw [show ((deformationFunctor n G 𝓞 ρ).toFunctor.map g u).1 =
        (repnQuotFunctor n G 𝓞).map g u.1 from rfl, ← hσq]
      exact hg
  · rintro ⟨R, σ, hσ, huniv⟩
    exact isCorepresentable_deformationFunctor_of_universalLift n G 𝓞 ρ R σ hσ huniv

end Deformations

end Deformation
