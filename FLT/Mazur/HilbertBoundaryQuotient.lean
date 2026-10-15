/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryOrbit
public import FLT.Mazur.RelativeRelationOrbitCoequalizer

/-!
# The closed boundary morphism of locally ringed quotients

The full original relation descends the entire boundary inclusion to a morphism
of locally ringed spaces over the unchanged coefficient base. Its underlying
map is the proved closed orbit embedding. Neither surjectivity on stalks nor
scheme effectivity follows from the topological closed embedding alone.
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
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

local notation "Q" => locallyRingedQuotient («p» := p) («q» := q)
local notation "Qc" => locallyRingedQuotient («p» := r) («q» := s)
local notation "P" => locallyRingedProjection («p» := p) («q» := q)
local notation "Pc" => locallyRingedProjection («p» := r) («q» := s)

local instance : Epi Pc := by
  dsimp only [locallyRingedProjection]
  infer_instance

/-- The full boundary inclusion gives a compatible locally ringed map to the original quotient. -/
theorem originalClosedQuotient_condition :
    (r).left.toLRSHom ≫ ((i).left.toLRSHom ≫ P) =
      (s).left.toLRSHom ≫ ((i).left.toLRSHom ≫ P) := by
  have h₁ := congrArg (fun v : C ⟶ A ↦ v.left.toLRSHom)
    (originalClosedArrow_fst f hL d V c k)
  have h₂ := congrArg (fun v : C ⟶ A ↦ v.left.toLRSHom)
    (originalClosedArrow_snd f hL d V c k)
  change (z).left.toLRSHom ≫ (p).left.toLRSHom = (r).left.toLRSHom ≫ (i).left.toLRSHom at h₁
  change (z).left.toLRSHom ≫ (q).left.toLRSHom = (s).left.toLRSHom ≫ (i).left.toLRSHom at h₂
  rw [← Category.assoc, ← h₁, Category.assoc, ← Category.assoc _ (i).left.toLRSHom,
    ← h₂, Category.assoc]
  exact congrArg (fun v ↦ (z).left.toLRSHom ≫ v) (coequalizer.condition _ _)

/-- The original boundary inclusion descends with its full structure-sheaf morphism. -/
def originalClosedQuotientMap : Qc ⟶ Q :=
  coequalizer.desc ((i).left.toLRSHom ≫ P) (originalClosedQuotient_condition f hL d V c k)

/-- The descended map retains the whole original boundary inclusion. -/
@[reassoc]
theorem originalClosedQuotientMap_projection :
    Pc ≫ originalClosedQuotientMap f hL d V c k = (i).left.toLRSHom ≫ P :=
  coequalizer.π_desc _ _

/-- The boundary comparison is unique as a locally ringed morphism. -/
theorem originalClosedQuotientMap_unique (g : Qc ⟶ Q)
    (hg : Pc ≫ g = (i).left.toLRSHom ≫ P) :
    g = originalClosedQuotientMap f hL d V c k :=
  (cancel_epi Pc).mp (hg.trans (originalClosedQuotientMap_projection f hL d V c k).symm)

/-- The descended morphism agrees with the full closed orbit comparison on every point. -/
theorem originalClosedQuotientMap_orbit (x : Qc) :
    locallyRingedOrbitHomeomorph e ((originalClosedQuotientMap f hL d V c k).base x) =
      originalClosedOrbitMap f hL d V c k (locallyRingedOrbitHomeomorph ec x) := by
  obtain ⟨y, rfl⟩ := locallyRingedProjection_surjective ec x
  have h := congrArg (fun v ↦ v.base y) (originalClosedQuotientMap_projection f hL d V c k)
  change (originalClosedQuotientMap f hL d V c k).base ((Pc).base y) =
    (P).base ((i).left y) at h
  rw [h, locallyRingedOrbitHomeomorph_projection, locallyRingedOrbitHomeomorph_projection,
    originalClosedOrbitMap_projection]

/-- The full locally ringed boundary morphism is a closed embedding on underlying spaces. -/
theorem originalClosedQuotientMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (originalClosedQuotientMap f hL d V c k).base := by
  have h : ⇑(originalClosedQuotientMap f hL d V c k).base =
      (locallyRingedOrbitHomeomorph e).symm ∘ originalClosedOrbitMap f hL d V c k ∘
        locallyRingedOrbitHomeomorph ec := by
    funext x
    apply (locallyRingedOrbitHomeomorph e).injective
    simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using
      originalClosedQuotientMap_orbit f hL d V c k x
  rw [h]
  exact (locallyRingedOrbitHomeomorph e).symm.isClosedEmbedding.comp
    ((originalClosedOrbitMap_isClosedEmbedding f hL d V c k).comp
      (locallyRingedOrbitHomeomorph ec).isClosedEmbedding)

/-- The descended closed inclusion retains the original coefficient morphism. -/
@[reassoc]
theorem originalClosedQuotientMap_base :
    originalClosedQuotientMap f hL d V c k ≫ locallyRingedBaseMap =
      locallyRingedBaseMap («p» := r) («q» := s) := by
  apply (cancel_epi Pc).mp
  rw [originalClosedQuotientMap_projection_assoc,
    locallyRingedProjection_baseMap, locallyRingedProjection_baseMap]
  exact congrArg Scheme.Hom.toLRSHom (Over.w i)

end FLT.Mazur.HilbertChart.AffineRestriction
