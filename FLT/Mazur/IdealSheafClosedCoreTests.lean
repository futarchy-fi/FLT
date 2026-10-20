/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafAffineTestErrors

/-!
# Constructed closed tests into open cores

The test ideal is pulled back once on the unchanged test scheme. Every power
then has a canonical map into any core containing its image. No test square
or kernel identification is required as additional data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IdealSheafClosedCoreTests
set_option backward.isDefEq.respectTransparency false
variable {X Y T : Scheme.{0}}

/-- Factor a map through an open containing its entire image. -/
def openLift (U : X.Opens) (f : T ⟶ X) (h : ⊤ ≤ f ⁻¹ᵁ U) : T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨f x, h (Set.mem_univ x)⟩, rfl⟩)

/-- The open factorization retains the original map. -/
@[reassoc]
theorem openLift_inclusion (U : X.Opens) (f : T ⟶ X) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    openLift U f h ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _

variable (I : X.IdealSheafData) (n : ℕ) (U : X.affineOpens)
  (C : (I ^ n).subscheme.Opens) (hC : (I ^ n).subschemeι ⁻¹ᵁ U.1 ≤ C)
  (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)

include hC hg in
/-- The full closed test lies in the chosen core, including all nilpotents. -/
theorem pulledMap_domain :
    ⊤ ≤ IdealSheafAffineTestErrors.pulledMap I n g ⁻¹ᵁ C :=
  (IdealSheafAffineTestErrors.closed_domain I (I.comap g) n U g hg
    (IdealSheafAffineTestErrors.pulledMap I n g)
    (IdealSheafAffineTestErrors.pulledMap_inclusion I n g)).trans
      ((TopologicalSpace.Opens.map
        (IdealSheafAffineTestErrors.pulledMap I n g).base).monotone hC)

/-- A canonical full test map into the open core. -/
def coreMap : ((I.comap g) ^ n).subscheme ⟶ C.toScheme :=
  openLift C (IdealSheafAffineTestErrors.pulledMap I n g)
    (pulledMap_domain I n U C hC g hg)

/-- Its square to the unchanged original source is proved by construction. -/
@[reassoc]
theorem coreMap_inclusion :
    coreMap I n U C hC g hg ≫ C.ι ≫ (I ^ n).subschemeι =
      ((I.comap g) ^ n).subschemeι ≫ g := by
  rw [← Category.assoc, coreMap, openLift_inclusion,
    IdealSheafAffineTestErrors.pulledMap_inclusion]

/-- At every order the test kernel is the power of one fixed original ideal. -/
theorem test_kernel [IsAffine T] :
    RingHom.ker (((I.comap g) ^ n).subschemeι.appTop.hom) =
      ((I.comap g).ideal ⟨⊤, isAffineOpen_top T⟩) ^ n := by
  exact ((I.comap g) ^ n).ker_subschemeι_app ⟨⊤, isAffineOpen_top T⟩

end FLT.Mazur.IdealSheafClosedCoreTests
