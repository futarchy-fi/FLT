/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeUnpointedFppfOpenNaturality

/-!
# The unpointed acyclic Picard open represents every further test

Membership of the restricted actual section in the local acyclic subsheaf
is represented by unique factorization through an actual scheme open.
No global line representative and no section of the original family is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- Every restricted section is locally acyclic exactly when the test factors into the open. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_represents
    {T U : Over (Spec (.of R))} (b : U ⟶ T)
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    (relativeFppfSheaf f).obj.map b.op s ∈
        (localGeometricAcyclicFppfSubfunctor f).obj (op U) ↔
      ∃! k : U.left ⟶ (finiteTypeUnpointedFppfAcyclicOpen f T s).toScheme,
        k ≫ (finiteTypeUnpointedFppfAcyclicOpen f T s).ι = b.left := by
  rw [← finiteTypeUnpointedFppfAcyclicOpen_eq_top, finiteTypeUnpointedFppfAcyclicOpen_map]
  have hm : b.left ⁻¹ᵁ finiteTypeUnpointedFppfAcyclicOpen f T s = ⊤ ↔
      ∀ u : U.left, b.left u ∈ finiteTypeUnpointedFppfAcyclicOpen f T s := by
    rw [SetLike.ext'_iff]
    exact Set.eq_univ_iff_forall
  rw [hm]
  constructor
  · intro hu
    have hr : Set.range b.left ⊆ Set.range (finiteTypeUnpointedFppfAcyclicOpen f T s).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨u, rfl⟩
      exact hu u
    refine ⟨IsOpenImmersion.lift _ b.left hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro k hk
    rw [← cancel_mono (finiteTypeUnpointedFppfAcyclicOpen f T s).ι, hk,
      IsOpenImmersion.lift_fac]
  · rintro ⟨k, hk, _⟩ u
    rw [← hk]
    exact (k u).property

/-- The open equipped with its original map to the original base. -/
def finiteTypeUnpointedFppfOpenTest (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) : Over (Spec (.of R)) :=
  Over.mk ((finiteTypeUnpointedFppfAcyclicOpen f T s).ι ≫ T.hom)

/-- The representing open's inclusion is an actual morphism of original test schemes. -/
def finiteTypeUnpointedFppfOpenArrow (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) : finiteTypeUnpointedFppfOpenTest f T s ⟶ T :=
  Over.homMk (finiteTypeUnpointedFppfAcyclicOpen f T s).ι

/-- The unique factorization also holds in the original relative test category. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_represents_over
    {T U : Over (Spec (.of R))} (b : U ⟶ T)
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    (relativeFppfSheaf f).obj.map b.op s ∈
        (localGeometricAcyclicFppfSubfunctor f).obj (op U) ↔
      ∃! k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s,
        k ≫ finiteTypeUnpointedFppfOpenArrow f T s = b := by
  rw [finiteTypeUnpointedFppfAcyclicOpen_represents]
  constructor
  · rintro ⟨k, hk, hu⟩
    let l : U ⟶ finiteTypeUnpointedFppfOpenTest f T s := Over.homMk k (by
      change k ≫ (finiteTypeUnpointedFppfAcyclicOpen f T s).ι ≫ T.hom = U.hom
      rw [← Category.assoc, hk, Over.w])
    refine ⟨l, Over.OverMorphism.ext hk, ?_⟩
    intro m hm
    exact Over.OverMorphism.ext (hu m.left (congrArg Over.Hom.left hm))
  · rintro ⟨k, hk, _⟩
    refine ⟨k.left, congrArg Over.Hom.left hk, ?_⟩
    intro l hl
    apply (cancel_mono (finiteTypeUnpointedFppfAcyclicOpen f T s).ι).mp
    exact hl.trans (congrArg Over.Hom.left hk).symm

end FLT.Mazur.CartierAbel
