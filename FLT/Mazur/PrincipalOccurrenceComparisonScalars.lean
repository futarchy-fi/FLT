/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAtlasQuotientEquations
public import FLT.Mazur.AffineScalarMap

/-!
# Scalar compatibility of the concrete atlas comparison maps

Every finite occurrence map preserves the coefficient spectrum. The same
holds for the two routes through a cross-chart intersection, so their
actual coordinate maps are algebra maps over the original coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)




/-- Finite occurrence embeddings preserve coefficients. -/
@[reassoc] theorem principalOccurrenceOpen_base (i : ι) (k : J i) :
    principalOccurrenceOpen x hx i k ≫ AffineScalarMap.base R (Stage R (A i) (x.source i)) =
      AffineScalarMap.base R
        (PrincipalStage R (B (dst i k)) (b (dst i k)) (x.target (dst i k))) := by
  rw [principalOccurrenceOpen_eq_spec]
  exact AffineScalarMap.map_fac (principalOccurrenceAmbientHom x i k)

/-- Identifying an overlap label preserves the same coefficient triangle. -/
@[reassoc] theorem principalOccurrenceOpenAt_base {j : κ}
    (i : ι) (k : J i) (hk : dst i k = j) :
    principalOccurrenceOpenAt e x hx i k hk ≫
        AffineScalarMap.base R (Stage R (A i) (x.source i)) =
      AffineScalarMap.base R (PrincipalStage R (B j) (b j) (x.target j)) := by
  subst j
  exact principalOccurrenceOpen_base e x hx i k

/-- Both overlap arrows of a finite patch give the same coefficient map. -/
@[reassoc] theorem principalOccurrencePatch_base :
    principalOccurrencePatchOther x hx p ≫ AffineScalarMap.base R
        (PrincipalStage R (B (dst p.1.val.1 p.2)) (b (dst p.1.val.1 p.2))
          (x.target (dst p.1.val.1 p.2))) =
      principalOccurrencePatchOpen x hx p ≫
        AffineScalarMap.base R (PrincipalStage R (B j) (b j) (x.target j)) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  rw [← principalOccurrenceOpen_base e x hx i l,
    ← principalOccurrenceOpen_base e x hx i k, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ AffineScalarMap.base R (Stage R (A i) (x.source i)))
    (principalOccurrencePatch_isPullback x hx i k l).w.symm

/-- The left outer restriction has the shared-overlap coefficient morphism. -/
@[reassoc] theorem principalOccurrenceCrossOuterLeft_base :
    principalOccurrenceCrossOuterLeft x hx p q ≫ AffineScalarMap.base R
        (PrincipalStage R (B (dst p.1.val.1 p.2)) (b (dst p.1.val.1 p.2))
          (x.target (dst p.1.val.1 p.2))) =
      principalOccurrenceCrossOpen x hx p q ≫
        AffineScalarMap.base R (PrincipalStage R (B j) (b j) (x.target j)) := by
  simp only [principalOccurrenceCrossOuterLeft, principalOccurrenceCrossOpen, Category.assoc,
    principalOccurrencePatch_base e x hx p]

/-- The right outer restriction has that very same coefficient morphism. -/
@[reassoc] theorem principalOccurrenceCrossOuterRight_base :
    principalOccurrenceCrossOuterRight x hx p q ≫ AffineScalarMap.base R
        (PrincipalStage R (B (dst q.1.val.1 q.2)) (b (dst q.1.val.1 q.2))
          (x.target (dst q.1.val.1 q.2))) =
      principalOccurrenceCrossOpen x hx p q ≫
        AffineScalarMap.base R (PrincipalStage R (B j) (b j) (x.target j)) := by
  simp only [principalOccurrenceCrossOuterRight, Category.assoc,
    principalOccurrencePatch_base e x hx q, principalOccurrenceCross_right_fac_assoc]

/-- The principal coordinate isomorphism respects the coefficient map. -/
theorem principalOccurrenceCrossCoordinates_base :
    (principalOccurrenceCrossIso x hx p q).inv ≫ principalOccurrenceCrossOpen x hx p q ≫
        AffineScalarMap.base R (PrincipalStage R (B j) (b j) (x.target j)) =
      AffineScalarMap.base R (PrincipalOccurrenceCrossRing x p q) := by
  rw [← principalOccurrenceCrossIso_fac, Category.assoc, Iso.inv_hom_id_assoc]
  exact AffineScalarMap.inclusion_fac _

/-- The actual left comparison route preserves every coefficient. -/
theorem principalOccurrenceCrossComparisonLeft_base (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    ((principalOccurrenceCrossIso x hx p q).inv ≫
        principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk) ≫
        AffineScalarMap.base R (Stage R (A i) (x.source i)) =
      AffineScalarMap.base R (PrincipalOccurrenceCrossRing x p q) := by
  simp only [Category.assoc, principalOccurrenceOpenAt_base,
    principalOccurrenceCrossOuterLeft_base]
  exact principalOccurrenceCrossCoordinates_base e x hx p q

/-- The actual right comparison route preserves every coefficient. -/
theorem principalOccurrenceCrossComparisonRight_base (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    ((principalOccurrenceCrossIso x hx p q).inv ≫
        principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl) ≫
        AffineScalarMap.base R (Stage R (A i) (x.source i)) =
      AffineScalarMap.base R (PrincipalOccurrenceCrossRing x p q) := by
  simp only [Category.assoc, principalOccurrenceOpenAt_base,
    principalOccurrenceCrossOuterRight_base]
  exact principalOccurrenceCrossCoordinates_base e x hx p q

/-- The left concrete comparison as an algebra map, with scalar compatibility proved. -/
def principalOccurrenceCrossComparisonLeftAlg (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    Stage R (A i) (x.source i) →ₐ[R] PrincipalOccurrenceCrossRing x p q :=
  AffineScalarMap.ofHom _ (principalOccurrenceCrossComparisonLeft_base e x hx p q i k hk)

/-- The right concrete comparison as an algebra map, with scalar compatibility proved. -/
def principalOccurrenceCrossComparisonRightAlg (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    Stage R (A i) (x.source i) →ₐ[R] PrincipalOccurrenceCrossRing x p q :=
  AffineScalarMap.ofHom _ (principalOccurrenceCrossComparisonRight_base e x hx p q i l hl)

end FLT.Mazur.FiniteTypeRelationModel
