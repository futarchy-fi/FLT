/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteSelectorKernel
public import FLT.Mazur.SchemeRelationSeedGenericCriterion

/-!
# Nonsplit finite-model seed certificates from original representatives

Division of representative arrows supplies an original arrow for every finite-model
kernel test. Pulling this arrow to any seed supplies its full comparison
inverse. Original source orbits over every coefficient point hit every
nonempty seed fiber. No full-envelope, image or orbit certificate is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "m" => pullback.lift (Over.Hom.left p) (Over.Hom.left q) h
local notation "H" => finiteSelector_isPullback f hL d V c k

/-- A literal original arrow, defined on the entire finite-model coefficient kernel. -/
def finiteSelectorKernelInverse
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    pullback v v ⟶ (relation f hL d V c k).left :=
  (H r hr hi).lift (pullback.fst v v) (pullback.snd v v) pullback.condition

/-- The constructed arrow preserves the full coefficient-kernel scheme, not only its points. -/
@[reassoc]
theorem finiteSelectorKernelInverse_comp
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    finiteSelectorKernelInverse f hL d V c k r hr hi ≫ m = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
    exact (H r hr hi).lift_fst _ _ _
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
    exact (H r hr hi).lift_snd _ _ _

/-- Every original kernel point has the constructed original relation preimage. -/
theorem finiteSelectorKernel_image
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left)
    (x : (pullback v v : Scheme)) : x ∈ Set.range m :=
  ⟨finiteSelectorKernelInverse f hL d V c k r hr hi x,
    congrArg (fun g ↦ g x) (finiteSelectorKernelInverse_comp f hL d V c k r hr hi)⟩

variable {Z : Scheme} (a : Z ⟶ A.left)
local notation "C" => (pullback (a ≫ v) (a ≫ v) : Scheme)
local notation "s" => SchemeRelationSeedKernelTransport.seedComparison v h a

/-- Pull the reconstructed original arrow into the two independent seed coordinates. -/
def finiteSelectorSeedInverse
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : C ⟶
    SchemeRelationRestriction.doubleDomain (p).left (q).left a :=
  SchemeRelationSeedKernelTransport.squareLift v h a
    (SchemeRelationSeedKernelTransport.seedToOriginalKernel v a ≫
      finiteSelectorKernelInverse f hL d V c k r hr hi) (𝟙 C) (by
        rw [Category.assoc, finiteSelectorKernelInverse_comp,
          Category.comp_id, Category.id_comp])

/-- The seed certificate is an actual inverse morphism on its entire scheme kernel. -/
@[reassoc]
theorem finiteSelectorSeedInverse_comp
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    finiteSelectorSeedInverse f hL d V c k a r hr hi ≫ s =
    𝟙 C := SchemeRelationSeedKernelTransport.squareLift_comparison ..

/-- All seed kernel branches have constructed certificates, without monicity of the seed. -/
theorem finiteSelectorSeed_image
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) (z : C) : z ∈ Set.range s :=
  ⟨finiteSelectorSeedInverse f hL d V c k a r hr hi z,
    congrArg (fun g ↦ g z) (finiteSelectorSeedInverse_comp f hL d V c k a r hr hi)⟩

/-- A nonempty seed fiber meets every original source orbit over that coefficient point. -/
theorem finiteSelectorSeed_orbits
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left)
    (z : Z) (x : A.left) (hx : v x = (a ≫ v) z) :
    ∃ y : Z, RelativeRelationOrbit.Related p q x (a y) := by
  apply (SchemeRelationMonicSeedKernel.mem_branch_iff_related a x).mp
  exact SchemeRelationEtaleBranchPropagation.fiber_subset_branch (p).left (q).left v h a z
    (fun y _ ↦ finiteSelectorKernel_image f hL d V c k r hr hi y) x hx

end FLT.Mazur.HilbertChart.AffineRestriction
