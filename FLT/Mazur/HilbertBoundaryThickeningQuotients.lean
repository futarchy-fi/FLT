/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningTower
public import FLT.Mazur.RelativeRelationOrbitCoequalizer

/-!
# Locally ringed descent of the infinitesimal boundary tower

The entire tower descends to actual locally ringed coequalizers over the
original base, compatibly with its map to the original quotient. Structure
sheaf maps are retained at every order. This does not assert scheme effectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n

open RelativeRelationOrbit
local notation "Q" n:max => locallyRingedQuotient (p := r n) (q := s n)
local notation "P" n:max => locallyRingedProjection (p := r n) (q := s n)
local notation "Q₀" => locallyRingedQuotient
  (p := fst f hL d V c k) (q := snd f hL d V c k)
local notation "P₀" => locallyRingedProjection
  (p := fst f hL d V c k) (q := snd f hL d V c k)

attribute [local irreducible] originalThickenedSource originalThickenedSourceMap
  originalThickenedRelation originalThickenedFst originalThickenedSnd originalThickenedArrow

local instance projection_epi (n : ℕ) : Epi (P n) := by
  dsimp only [locallyRingedProjection]
  infer_instance

/-- The whole infinitesimal inclusion is compatible with the original coequalizer. -/
theorem originalThickenedQuotient_condition (n : ℕ) :
    (r n).left.toLRSHom ≫ ((i n).left.toLRSHom ≫ P₀) =
      (s n).left.toLRSHom ≫ ((i n).left.toLRSHom ≫ P₀) := by
  have h₁ := congrArg (fun v : C n ⟶ A ↦ v.left.toLRSHom)
    (originalThickenedArrow_fst f hL d V c k n)
  have h₂ := congrArg (fun v : C n ⟶ A ↦ v.left.toLRSHom)
    (originalThickenedArrow_snd f hL d V c k n)
  change (z n).left.toLRSHom ≫ (fst f hL d V c k).left.toLRSHom =
    (r n).left.toLRSHom ≫ (i n).left.toLRSHom at h₁
  change (z n).left.toLRSHom ≫ (snd f hL d V c k).left.toLRSHom =
    (s n).left.toLRSHom ≫ (i n).left.toLRSHom at h₂
  rw [← Category.assoc, ← h₁, Category.assoc,
    ← Category.assoc _ (i n).left.toLRSHom, ← h₂, Category.assoc]
  exact congrArg (fun v ↦ (z n).left.toLRSHom ≫ v) (coequalizer.condition _ _)

/-- Every infinitesimal neighborhood maps to the original locally ringed quotient. -/
def originalThickenedQuotientMap (n : ℕ) : Q n ⟶ Q₀ :=
  coequalizer.desc ((i n).left.toLRSHom ≫ P₀)
    (originalThickenedQuotient_condition f hL d V c k n)

/-- The descended morphism retains the whole original infinitesimal inclusion. -/
@[reassoc]
theorem originalThickenedQuotientMap_projection (n : ℕ) :
    P n ≫ originalThickenedQuotientMap f hL d V c k n = (i n).left.toLRSHom ≫ P₀ :=
  coequalizer.π_desc _ _

/-- The infinitesimal quotient comparison is over the unchanged coefficient scheme. -/
@[reassoc]
theorem originalThickenedQuotientMap_base (n : ℕ) :
    originalThickenedQuotientMap f hL d V c k n ≫ locallyRingedBaseMap =
      locallyRingedBaseMap (p := r n) (q := s n) := by
  apply (cancel_epi (P n)).mp
  rw [originalThickenedQuotientMap_projection_assoc,
    locallyRingedProjection_baseMap, locallyRingedProjection_baseMap]
  exact congrArg Scheme.Hom.toLRSHom (Over.w (i n))

/-- Source transitions equalize the full relation at the preceding order. -/
theorem originalThickenedQuotientTransition_condition {m n : ℕ} (h : m ≤ n) :
    (r m).left.toLRSHom ≫
        ((originalThickenedTransition f hL d V c k h).left.toLRSHom ≫ P n) =
      (s m).left.toLRSHom ≫
        ((originalThickenedTransition f hL d V c k h).left.toLRSHom ≫ P n) := by
  have h₁ := congrArg (fun v : C m ⟶ B n ↦ v.left.toLRSHom)
    (originalThickenedRelationTransition_fst f hL d V c k h)
  have h₂ := congrArg (fun v : C m ⟶ B n ↦ v.left.toLRSHom)
    (originalThickenedRelationTransition_snd f hL d V c k h)
  change (originalThickenedRelationTransition f hL d V c k h).left.toLRSHom ≫
    (r n).left.toLRSHom = (r m).left.toLRSHom ≫
      (originalThickenedTransition f hL d V c k h).left.toLRSHom at h₁
  change (originalThickenedRelationTransition f hL d V c k h).left.toLRSHom ≫
    (s n).left.toLRSHom = (s m).left.toLRSHom ≫
      (originalThickenedTransition f hL d V c k h).left.toLRSHom at h₂
  rw [← Category.assoc, ← h₁, Category.assoc,
    ← Category.assoc _ (originalThickenedTransition f hL d V c k h).left.toLRSHom,
    ← h₂, Category.assoc]
  exact congrArg (fun v ↦
    (originalThickenedRelationTransition f hL d V c k h).left.toLRSHom ≫ v)
    (coequalizer.condition _ _)

/-- The actual locally ringed transition, including its structure sheaf map. -/
def originalThickenedQuotientTransition {m n : ℕ} (h : m ≤ n) : Q m ⟶ Q n :=
  coequalizer.desc ((originalThickenedTransition f hL d V c k h).left.toLRSHom ≫ P n)
    (originalThickenedQuotientTransition_condition f hL d V c k h)

/-- Quotient transitions recover the whole source transition on the original projection. -/
@[reassoc]
theorem originalThickenedQuotientTransition_projection {m n : ℕ} (h : m ≤ n) :
    P m ≫ originalThickenedQuotientTransition f hL d V c k h =
      (originalThickenedTransition f hL d V c k h).left.toLRSHom ≫ P n :=
  coequalizer.π_desc _ _

/-- The tower commutes with the map to the unchanged original quotient. -/
@[reassoc]
theorem originalThickenedQuotientTransition_map {m n : ℕ} (h : m ≤ n) :
    originalThickenedQuotientTransition f hL d V c k h ≫
      originalThickenedQuotientMap f hL d V c k n =
      originalThickenedQuotientMap f hL d V c k m := by
  apply (cancel_epi (P m)).mp
  rw [originalThickenedQuotientTransition_projection_assoc,
    originalThickenedQuotientMap_projection, originalThickenedQuotientMap_projection]
  have he := congrArg (fun v : B m ⟶ A ↦ v.left.toLRSHom)
    (originalThickenedTransition_source f hL d V c k h)
  rw [← Category.assoc]
  exact congrArg (fun v ↦ v ≫ P₀) he

/-- Every descended transition is over the unchanged original coefficient scheme. -/
@[reassoc]
theorem originalThickenedQuotientTransition_base {m n : ℕ} (h : m ≤ n) :
    originalThickenedQuotientTransition f hL d V c k h ≫
      locallyRingedBaseMap (p := r n) (q := s n) =
      locallyRingedBaseMap (p := r m) (q := s m) := by
  rw [← originalThickenedQuotientMap_base f hL d V c k n,
    originalThickenedQuotientTransition_map_assoc, originalThickenedQuotientMap_base]

/-- The descended maps obey the same cocycle as the original infinitesimal tower. -/
@[reassoc]
theorem originalThickenedQuotientTransition_comp {l m n : ℕ}
    (h₁ : l ≤ m) (h₂ : m ≤ n) :
    originalThickenedQuotientTransition f hL d V c k h₁ ≫
      originalThickenedQuotientTransition f hL d V c k h₂ =
      originalThickenedQuotientTransition f hL d V c k (h₁.trans h₂) := by
  apply (cancel_epi (P l)).mp
  rw [originalThickenedQuotientTransition_projection_assoc,
    originalThickenedQuotientTransition_projection, originalThickenedQuotientTransition_projection]
  have he := congrArg (fun v : B l ⟶ B n ↦ v.left.toLRSHom)
    (originalThickenedTransition_comp f hL d V c k h₁ h₂)
  rw [← Category.assoc]
  exact congrArg (fun v ↦ v ≫ P n) he

/-- Equal-order transitions remain identities as locally ringed morphisms. -/
theorem originalThickenedQuotientTransition_refl (n : ℕ) :
    originalThickenedQuotientTransition f hL d V c k (le_refl n) = 𝟙 _ := by
  apply (cancel_epi (P n)).mp
  rw [originalThickenedQuotientTransition_projection, originalThickenedTransition_refl]
  change 𝟙 _ ≫ P n = P n ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

end FLT.Mazur.HilbertChart.AffineRestriction
