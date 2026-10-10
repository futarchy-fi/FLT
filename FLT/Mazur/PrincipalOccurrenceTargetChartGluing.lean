/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceActualCoverRoutes
public import FLT.Mazur.PrincipalOccurrenceSubfamilyGluing

/-!
# Glued routes from overlaps into chosen ambient charts

Target-compatible patches give actual maps into a target chart. Descent
of their original cover and all pairwise comparison equations glues them
at one bijective stage. No compatibility of the finite maps is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport

universe u v w z z' z''

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))




/-- A target-compatible patch has its concrete route through the outer overlap. -/
def principalOccurrenceTargetPatchMap {j : κ} (i : ι)
    (p : PrincipalOccurrencePatchTo (dst := dst) j i) :
    principalOccurrencePatchScheme x p.1 ⟶ Spec (.of (Stage R (A i) (x.source i))) :=
  principalOccurrencePatchOther x hx p.1 ≫ principalOccurrenceOpenAt e x hx i p.2.val p.2.property

variable {j : κ} (i : ι)
  (hc : (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
    (principalOccurrencePatchOpen x hx p.1).opensRange) = ⊤)
  (he : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i q.2.val q.2.property)

attribute [local irreducible] principalOccurrencePatchOpen principalOccurrenceOpenAt
  principalOccurrencePatchOther

/-- Glue the concrete target routes on exactly the target-compatible patch family. -/
def principalOccurrenceTargetChartGlue :
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶
      Spec (.of (Stage R (A i) (x.source i))) :=
  principalOccurrencePatchSubfamilyGlue x hx
    (fun p : PrincipalOccurrencePatchTo (dst := dst) j i ↦ p.1) hc
    (principalOccurrenceTargetPatchMap e x hx i) (by
      intro p q
      simpa only [principalOccurrenceTargetPatchMap, principalOccurrenceCrossOuterLeft,
        principalOccurrenceCrossOuterRight, Category.assoc] using he p q)

/-- The glued chart map restricts to every concrete outer-label route. -/
@[reassoc] theorem principalOccurrenceTargetChartGlue_fac
    (p : PrincipalOccurrencePatchTo (dst := dst) j i) :
    principalOccurrencePatchOpen x hx p.1 ≫ principalOccurrenceTargetChartGlue e x hx i hc he =
      principalOccurrenceTargetPatchMap e x hx i p :=
  principalOccurrencePatchSubfamilyGlue_fac _ _ _ _ _ _ _

variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]
  (t : κ → ι) (c : ∀ j, PrincipalIncoming (dst := dst) j)
  (hcover : ∀ j, (principalOccurrenceOriginalOpen e (c j).val.1 (c j).val.2).opensRange ≤
    ⨆ l : {l : J (c j).val.1 // ∃ k : J (t j), dst (t j) k = dst (c j).val.1 l},
      (principalOccurrenceOriginalOpen e (c j).val.1 l.val).opensRange)
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [∀ i, Mono (U i)]

include hcover hUV in
/-- Original atlas cover inclusions produce actual glued target-chart maps at one finite stage. -/
theorem exists_principalOccurrence_target_chart_gluing
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          ∃ g : ∀ j, Spec (.of (PrincipalStage R (B j) (b j) (y.target j))) ⟶
              Spec (.of (Stage R (A (t j)) (y.source (t j)))),
            ∀ j (p : PrincipalOccurrencePatchTo (dst := dst) j (t j)),
              principalOccurrencePatchOpen y hy p.1 ≫ g j =
                principalOccurrenceTargetPatchMap e y hy (t j) p := by
  obtain ⟨y, hxy, hs, hy, hcy, he⟩ := exists_principalOccurrence_actual_covers_routes e x
    (μ := fun j ↦ PrincipalOccurrencePatchTo (dst := dst) j (t j))
    (ν := fun j ↦ PrincipalOccurrencePatchTo (dst := dst) j (t j) ×
      PrincipalOccurrencePatchTo (dst := dst) j (t j))
    (fun _ p ↦ p.1) (fun j ↦ principalOccurrenceOriginalPatchTo_cover e (t j) (c j) (hcover j))
    (fun _ n ↦ n.1.1) (fun _ n ↦ n.2.1) (fun j _ ↦ t j)
    (fun _ n ↦ n.1.2.val) (fun _ n ↦ n.2.2.val)
    (fun _ n ↦ n.1.2.property) (fun _ n ↦ n.2.2.property) U V hUV s
  refine ⟨y, hxy, hs, hy,
    fun j ↦ principalOccurrenceTargetChartGlue e y hy (t j) (hcy j)
      (fun p q ↦ he j (p, q)), fun j p ↦ ?_⟩
  exact principalOccurrenceTargetChartGlue_fac e y hy (t j) (hcy j)
    (fun p q ↦ he j (p, q)) p

end FLT.Mazur.FiniteTypeRelationModel
