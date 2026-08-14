# hub-lsb1u.10.2 — Galois representations attached to automorphic forms (second independent pass)

Independent cartography pass B. Sources: repo main working tree at `/Users/kas/FLT` (Lean +
blueprint), general knowledge, URL-verified web citations. No cartography/ or panel/ material
consulted.

---

## 1. What the repo actually has (anchors, quoted)

### 1.1 The quaternionic automorphy definition — the consumer of any attachment statement

`FLT/GaloisRepresentation/Automorphic.lean:67` defines `GaloisRep.IsAutomorphicOfLevel`.
Docstring (`Automorphic.lean:20-26`):

> "We say that a 2-dimensional p-adic or a mod p Galois representation of the absolute Galois
> of a totally real field number field F of even degree is *automorphic* if there exists a
> totally definite quaternion algebra D/F unramified at all finite places, a finite set S of
> finite places of F, and an automorphic form of level U_1(S) ... and weight 2 for D such that
> the Galois representation is associated to the form by the construction of Carayol, Taylor
> et al."

But the formal `Prop` **never invokes an attachment construction**. It asks only
(`Automorphic.lean:81-94`):

- existence of `D` (division, `IsQuaternionAlgebra F D`, with `WithRigidification`), discriminant 1;
- an eigencharacter `π : HeckeAlgebra (R := ℤ_[p]) D ⟨…, S, ∅, 1, …⟩ →ₐ[ℤ_[p]] A`
  (`Automorphic.lean:85`);
- for all **good** `v` (`↑p ∉ v.1`, `v ∉ S`, line 87):
  - `ρ.IsUnramifiedAt v` (line 89),
  - `(ρ.toLocal v (Frob v)).det = v.1.absNorm` (line 91, i.e. det = cyclotomic),
  - `trace = π (HeckeAlgebra.T … v …)` (lines 93-94).

So automorphy is a **pure Frobenius-eigensystem matching at good primes** (v ∤ p, v ∉ S).
The definition itself needs no theorem — it is `∃ D, ∃ π, ∀ good v, (unram ∧ det ∧ trace)`.
The doc note `Automorphic.lean:30-35` records the intended bad-place shape ("either Steinberg
or principal series π(χ₁,χ₂) with χᵢ tame and χ₁χ₂ unramified") but this is **not** in the Prop.

Supporting definitions:
- `GaloisRep` (continuous rep of `Γ K` on an `A`-module): `FLT/Deformations/RepresentationTheory/GaloisRep.lean:49`;
  `toLocal` :313, `IsUnramifiedAt` :320, `charFrob` :339, `IsFlatAt` :395, `IsIrreducible` :408.
- Hecke algebra: `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean` —
  `U₁Data` :375, `U₁` level :395, `HeckeAlgebra` :878, `HeckeAlgebra.T` :915, `HeckeAlgebra.U` :922.
- Compatible families: `FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean:38`
  (`GaloisRepFamily`), `:58` (`isCompatible` — "weakest possible concept": unramified + charpoly of
  `Frob_v` equals `(Pv v).map φ` for `v ∉ S`, `v ∤ p` only).

### 1.2 Where attachment content is consumed (the sorried absorbers)

1. `cyclic_base_change`, `FLT/GaloisRepresentation/Automorphic.lean:127-184`, `sorry` at :184.
   Statement: for `E/F` solvable, `ρ` over `ℚ_[p]ᵃˡᵍ` with (a) `hρirred` irreducible after
   restriction (:143), (b) `hρdet` det = cyclotomic (:145), (c) `hρflat` — an **integral model**
   `ρ₀` over a module-finite free local ℤ_p-algebra, `IsFlatAt` all `v | p` (:150-163),
   (d) unramified outside `S ∪ {p}` (:168), (e) `hρtame` — tame rank-1 quotient at each `w ∈ S`
   (:170-178) — then `IsAutomorphicOfLevel p _ _ S ↔` same over `E` at the pulled-back level (:180-183).
2. `IsHardlyRamified.mem_isCompatible`, `FLT/GaloisRepresentation/HardlyRamified/Family.lean:37-68`,
   `sorry` at :68: a hardly ramified p-adic `ρ` over ℚ lies in a compatible `GaloisRepFamily`
   whose odd-ℓ members are hardly ramified.
3. `IsHardlyRamified.lifts`, `HardlyRamified/Lift.lean:37-48`, `sorry` at :48 (mod-p → p-adic lift).
4. `mod_three` (`HardlyRamified/ModThree.lean:34`) and `three_adic` (`HardlyRamified/Threeadic.lean:39`)
   — downstream 3-adic endgame, attachment-free in statement.
5. Spine: `FLT/Proof.lean:98` `B4_proof : B4 := sorry` (Frey `E[p]` reducible).

The blueprint (`blueprint/src/chapter/ch04overview.tex`) shows the intended proofs of (1)-(3) run
through: potential modularity (Moret–Bailly + JL + converse theorems + a modularity lifting
theorem, lines 27-36), the modularity lifting theorem (`modularity_lifting_theorem`, :72-81) whose
`\uses` list **explicitly includes** `Galois_representation_from_automorphic_representation_on_GL_2_form`,
and the family step "Khare–Wintenberger … Brauer's theorem trick in \cite{blggt}" (:106-110).

### 1.3 The blueprint's attachment statement

`blueprint/src/chapter/chtopbestiary.tex:228`:

> "\begin{theorem}\label{Galois_representation_from_automorphic_representation_on_GL_2_form}
> ... Given an automorphic representation π for an inner form of GL_2 over a totally real field
> ... weight 2 discrete series at every infinite place, there exists a compatible family of
> 2-dimensional Galois representations associated to π, with S being the places at which π is
> ramified, and F_p(X) being the monic polynomial with roots the two Satake parameters for π at p."

Marked `\notready`; `\uses{automorphic_representation, Shimura_varieties, compatible_family}`.
Note it is a **good-primes-only, compatible-family** statement (Satake matching outside ram(π));
no bad-place local-global is asserted in the blueprint node either.

### 1.4 The Assumptions directory — the axiom is planned but not yet stated

`FLT/Assumptions/` contains only `Odlyzko.lean`, `Mazur.lean`, `KnownIn1980s.lean`.
`FLT/Assumptions/README.md`, "Forthcoming assumptions":

> "The next definition needs Hecke algebras.
> * The existence of a p-adic Galois representation attached to a weight 2 automorphic form over
>   a totally definite quaternion algebra."

and, three bullets later (JL, cyclic base change, automorphic induction):

> "I will probably rephrase all of these goals in terms of Galois representations which will
> avoid us having to define automorphic forms for GL_2 directly."

The Hecke algebras now exist (`Concrete.lean:878`), so the attachment axiom is **statable today**.
The escape hatch meanwhile is `FLT/Assumptions/KnownIn1980s.lean:79` `axiom knownin1980s {P : Prop} : P`,
whose docstring (:37-39, :68-69) names exactly this bead: "Taylor and others on attaching Galois
representations to Hilbert modular forms, Langlands on cyclic base change". One live use so far:
`FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean:499` (finiteness `[Δ_g : Fˣ] < ∞`, Voight 17.7.13).

---

## 2. Weakest sufficient attachment statement

**Which forms.** Only: weight 2, trivial infinity type, trivial central-character twist,
level `U₁(S)` (`U₁Data` with `Q = ∅`, character `1`), on a totally definite quaternion algebra
`D/F` of **discriminant 1** over a totally real `F` of **even degree**, `p` odd with
`2 < [F(ζ_p):F]` (the `hp` hypothesis, `Automorphic.lean:70`). Nothing else — no higher weight,
no ramified `D`, no `U₀`-type or nebentypus levels, no odd-degree `F`.

**Which compatibility.** Split into what each consumer forces:

- (W) *Weak/good-prime attachment* — enough to make `IsAutomorphicOfLevel` non-vacuous and to
  state modularity lifting: for every `π : HeckeAlgebra D 𝒮 →ₐ[ℤ_p] ℚ_pᵃˡᵍ` there is a
  continuous `ρ_π : GaloisRep F (ℚ_pᵃˡᵍ) (Fin 2 → ℚ_pᵃˡᵍ)` with, for all `v ∤ p`, `v ∉ S`:
  unramified, `tr ρ_π(Frob_v) = π(T_v)`, `det ρ_π(Frob_v) = N(v)`. This is exactly the
  conjunction quantified in `Automorphic.lean:87-94` read as a *construction* instead of a match.
- (I) *Integrality*: `ρ_π` conjugates into `GL₂(𝒪)` for `𝒪 ⊂ ℚ_pᵃˡᵍ` finite free over ℤ_p
  (needed to feed `hρflat`'s integral-model format, `Automorphic.lean:150-163`, and
  `mem_isCompatible`'s `A`-valued `τ`, `Family.lean:49-58`). Standard lattice/pseudo-rep argument
  given (W) + continuity + compactness.
- (Bℓ) *Bad places, ℓ ≠ p*: for `v ∈ S`, `ρ_π|_{G_v}` has a tame rank-one quotient
  (Steinberg or tame principal series — the shape in `Automorphic.lean:30-35` and hypothesis
  `hρtame`, `Automorphic.lean:170-178`). Full Carayol local-global is **not** needed; only this
  one-sided quotient shape is consumed.
- (Bp) *At p*: level prime to `p` (forced: `S` avoids `p` via `hS`, `Automorphic.lean:166`,
  and good-prime clause `↑p ∉ v.1`) ⇒ `ρ_π` is **flat** (`IsFlatAt`, Barsotti–Tate) at all
  `v | p` — consumed by `hρflat` and by `mem_isCompatible`'s hardly-ramified conclusion
  (`IsHardlyRamified` includes flatness at ℓ, `HardlyRamified/Defs.lean` comment block).
- *Not needed*: Frobenius-semisimplicity, full local Langlands matching at any place, weight-
  monodromy, ε-factor compatibility, families beyond the "weakest possible" `isCompatible`
  (charpoly at good primes only, `GaloisRepFamily.lean:58` docstring).

**Weakest sufficient package = (W) + (I) + (Bℓ-quotient) + (Bp-flat)** for the restricted form
class above. (W)+(I) alone suffice to *state* the modularity-lifting/base-change axioms; (Bℓ)+(Bp)
are needed the moment one wants the ⇐ direction of those axioms to be provable rather than
absorbed (they let one check the automorphic side satisfies the hypotheses one is matching against).

---

## 3. Numbered node inventory

Sizes: S ≤ 1 wk, M ≈ 1 person-month, L ≈ 1 quarter, XL = multi-year / out of scope (axiom).

| # | Node | Content | Size | Status |
|---|------|---------|------|--------|
| G1 | `IsAutomorphicOfLevel` statement | done at `Automorphic.lean:67` | S | **done** (modulo G2) |
| G2 | `IsQuaternionAlgebra E (E ⊗[F] D)` instance | `Automorphic.lean:100` `sorry -- Ask Edison?` | S | sorried; genuine gap in defn hygiene |
| G3 | Attachment axiom, statement (W)+(I) | new file `FLT/Assumptions/GaloisRepAttach.lean` (or similar); quantify over `π : HeckeAlgebra D 𝒮 →ₐ[ℤ_p] A` as in `Automorphic.lean:85` | S-M to state | not stated; README flags it "forthcoming" |
| G4 | Attachment axiom, bad-place clause (Bℓ) | tame rank-1 quotient at `v ∈ S`, format copied from `hρtame` `Automorphic.lean:170-178` | S extra | not stated |
| G5 | Attachment axiom, p-clause (Bp) | `IsFlatAt v` for `v \| p`, format from `hρflat` `Automorphic.lean:150-163` (needs G3's integral model) | M extra (flatness defn already exists, `GaloisRep.lean:387-395`) | not stated |
| G6 | Attachment **proof**, Eichler–Shimura route (F = ℚ analogue) | not usable: repo forces even-degree F, totally definite D; classical modular curves don't appear | — | ruled out by the repo's definitions |
| G7 | Attachment proof, Carayol route | Shimura curves need D split at exactly one infinite place — **the repo's D is totally definite**, so Carayol applies only after JL transfer to GL₂ and back | XL | axiom forever (project policy) |
| G8 | Attachment proof, Taylor route | Taylor 1989 handles even-degree F by congruences + pseudo-reps from the odd-degree/Carayol case; input is a Hilbert eigenform on **GL₂**, so JL is still the bridge from the quaternionic `HeckeAlgebra` eigencharacter | XL | axiom forever |
| G9 | `cyclic_base_change` | `Automorphic.lean:127-184`, sorry :184 | XL (absorbing axiom) | statement done |
| G10 | `mem_isCompatible` | `Family.lean:37-68`, sorry :68 | XL (absorbing; contains **post-1990** content — see risks) | statement done |
| G11 | `IsHardlyRamified.lifts` | `Lift.lean:37-48`, sorry :48 | XL (absorbing; Khare–Wintenberger-flavoured) | statement done |
| G12 | Modularity lifting theorem, Lean statement | blueprint `modularity_lifting_theorem` (ch04overview.tex:72-81); "stating this theorem in Lean is the first target" (:120). All ingredients (`IsAutomorphicOfLevel`, `IsFlatAt`, tame-quotient format) now exist | M | not in Lean yet |
| G13 | Blueprint bestiary node `Galois_representation_from_automorphic_representation_on_GL_2_form` | chtopbestiary.tex:228, `\notready`; compatible-family form; will likely be **superseded** by G3-G5 (quaternionic Hecke form) per README's rephrasing plan | S (doc reconciliation) | blueprint only |
| G14 | Bib hygiene | `blueprint/src/FLT.bib` has Taylor–Wiles (:34), taylor-mero-cont (:51), DDT (:166) but **no Carayol 1986, no Taylor 1989, no Blasius–Rogawski** | S | missing |

### Dependency edges

- G3 ← G1 (defn), ← `HeckeAlgebra` (`Concrete.lean:878`), ← `GaloisRep` (`GaloisRep.lean:49`).
- G4 ← G3; format ← `localTameAbelianInertiaGroup` (used `Automorphic.lean:176`).
- G5 ← G3 + `IsFlatAt` (`GaloisRep.lean:395`).
- G9 ← G3 (+G4, G5 to be provable); G9 also ← JL + Langlands base change + multiplicity one
  (blueprint ch04overview.tex:98-104, chtopbestiary.tex:212-214) — **edge into JL hub-lsb1u.4**.
- G10 ← G3-G5 + potential modularity (Moret–Bailly node) + G12 + Brauer/BLGGT trick.
- G11 ← G10-adjacent machinery (KW lifting).
- G12 ← G1, G3; blueprint `\uses` also lists Galois cohomology nodes + `moret-bailly` — edges to
  the patching/deformation hubs (`FLT/Patching/`, `FLT/Deformations/` are substantial and live).
- `Proof.lean:98 (B4)` ← Frey hardly-ramified (`HardlyRamified/Frey.lean:39-46`, sorried) ← G10/G11
  chain ← G9 ← G3.

### Mathlib anchors

- `Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter` (imported `Automorphic.lean:11`; used at :146).
- `Mathlib.NumberTheory.Padics.Complex` (`PadicAlgCl p`, spectral norm; `Automorphic.lean:12,103`).
- `IsDedekindDomain.HeightOneSpectrum` (places), `LinearMap.charpoly`/`trace`/`det`,
  `Module.Free/Finite` rank-2 formalism, `AlgebraicClosure ℚ_[p]`, `ContinuousSMul`,
  `IsModuleTopology` (FLT-local, heavily used in integral models).
- No Mathlib Shimura varieties / étale cohomology of curves at the needed level — confirms
  proof-side (G7/G8) is out of reach; axiom is the only realistic route.

---

## 4. Citations (URL-verified)

1. H. Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*,
   Ann. Sci. ENS (4) 19 (1986), 409-468. doi:10.24033/asens.1512 (Numdam). Local-global at
   ℓ ≠ p via bad reduction of Shimura curves (companion: *Sur la mauvaise réduction des courbes
   de Shimura*, Compositio 59 (1986), 151-230). Requires an infinite place where D is split ⇒
   does not directly cover totally definite D.
2. R. Taylor, *On Galois representations associated to Hilbert modular forms*, Invent. Math. 98
   (1989), 265-280. doi:10.1007/BF01388853; https://eudml.org/doc/143729. Even-degree case via
   congruences + pseudo-representations — the case the repo lives in; pre-1990, so admissible
   under the `knownin1980s` policy.
3. D. Blasius, J. Rogawski, *Galois representations for Hilbert modular forms*, Bull. AMS 21
   (1989), 65-69 (announcement; alternative route, Invent. Math. 114 (1993) for motives).
4. T. Saito, *Hilbert modular forms and p-adic Hodge theory*, Compositio 145 (2009), 1081-1113.
   doi:10.1112/S0010437X09004175; arXiv:math/0612077. Local-global **at p** (under Carayol's
   assumption) — the honest reference for clause (Bp) in general; post-1990.
5. C. Breuil, *Une remarque sur les représentations locales p-adiques et les congruences entre
   formes modulaires de Hilbert*, Bull. SMF 127 (1999). https://www.numdam.org/articles/10.24033/bsmf.2357/ —
   flatness/BT at p in the weight-2 setting; also post-1990.

---

## 5. JL absorption context (hub-lsb1u.4) and ledger implications

The repo defines modularity **quaternionically only** (`Automorphic.lean:67`; blueprint
ch04overview.tex:13-20: "What we will mean by 'modular' is 'associated to an automorphic
representation of the units of the totally definite quaternion algebra...'"). Consequences:

1. **The attachment axiom (G3) is an ABSORBING axiom w.r.t. JL.** Every pre-1990 attachment
   theorem (Carayol, Taylor, Blasius–Rogawski) takes a Hilbert eigenform on GL₂ as input. The
   repo's input is an eigencharacter of the quaternionic `HeckeAlgebra` for totally definite D
   of discriminant 1. The literature statement transfers to that input **only through
   Jacquet–Langlands** (quaternionic eigensystem ↦ holomorphic Hilbert eigenform of weight 2).
   Stating G3 quaternionically therefore bakes one direction of JL into the axiom. This is
   *intentional*: `Assumptions/README.md` says the GL₂-facing goals (JL, base change, automorphic
   induction) will be "rephrase[d] ... in terms of Galois representations" to avoid defining
   GL₂ automorphic forms.
2. **Ledger rule to avoid double counting with hub-lsb1u.4:** if the ledger carries both a JL
   node and a quaternionic attachment node at full weight, JL is counted twice (once standalone,
   once hidden in G3). Either (a) state G3 for GL₂-forms + an explicit JL edge (repo has chosen
   not to), or (b) mark G3 "absorbs JL (one direction) + Taylor/Carayol attachment" and reduce
   the standalone JL node to the residual uses: multiplicity one and image-of-base-change
   classification inside G9 (blueprint chtopbestiary.tex:212-214 lists JL, mult 1, cyclic base
   change, automorphic induction as the four analytic inputs).
3. **G9 (`cyclic_base_change`) is a second absorber**: its iff-statement quietly contains
   Langlands base change, JL (again), multiplicity one, and *both* directions of attachment
   (to transport "automorphic" across E/F one characterises which eigensystems arise). If G3 and
   G9 are both ledger axioms, the JL/attachment content appears in **three** places (G3, G9, G10).
   The ledger should credit it once and mark the other occurrences "shared content with G3".

---

## 6. Risks

- **Post-1990 leakage at p (medium-high).** Clause (Bp) flatness for totally definite-D forms:
  general references are Saito 2009 / Breuil 1999 / Liu. A pre-1990 derivation exists in the good
  cases needed (level prime to p, weight 2, via congruences and Carayol's good-reduction models +
  Raynaud), but is folklore-shaped; the `knownin1980s` policy (`KnownIn1980s.lean:16-29`) requires
  a written justification and KMB's sign-off. If it fails the 1980s test, G5 must be a *separate*
  post-1990 assumption — ledger category change.
- **G10/G11 are not 1980s theorems at all.** The blueprint route uses Khare–Wintenberger-style
  lifting and the BLGGT Brauer trick (ch04overview.tex:106-110, `\cite{blggt}` = 2014). These
  sorries will become *modern* assumptions or long proofs; do not book them under the same ledger
  class as G3. (KMB's own phase-2 plan, `KnownIn1980s.lean:43-48`, anticipates ~10 pinned axioms.)
- **Even-degree/discriminant-1 rigidity (low, but real).** `IsAutomorphicOfLevel` hard-codes
  discriminant 1 (hence even degree). Any future need for an auxiliary ramified D (e.g. level-
  raising at a prime, standard in Skinner–Wiles-type arguments) breaks the definition, not just
  a proof.
- **G2 (`sorry` instance at `Automorphic.lean:100`) sits inside the base-change statement**; a
  wrong instance here would make G9's statement subtly wrong. Small but should be cleared before
  G9 is pinned as an axiom.
- **Statement-format risk in G3.** The `A`-valued form (`π : … →ₐ[ℤ_p] A` for general topological
  ℤ_p-algebras `A`) is stronger than the literature's `ℚ_pᵃˡᵍ`-valued statement; state G3 for
  `A = ℚ_pᵃˡᵍ` + integrality (I) and derive the rest, otherwise the axiom over-asserts.
- **Size honesty.** Statement work (G3-G5, G12, G14): S/M each, ~1-2 person-months total, all
  unblocked today. Proof work (G7/G8): XL, multi-year, correctly out of scope — the project's
  own README treats attachment as a permanent 1980s assumption for phase 1.

## 7. Verdict

Statement-side: **M overall** (attachment axiom family G3-G5 statable now against existing
`HeckeAlgebra` + `GaloisRep` infrastructure; G12 statement M). Proof-side: **XL, permanently
axiomatised** by project policy. The bead's real deliverable is the axiom *statement* plus a
ledger annotation that G3 absorbs one direction of JL and that G9/G10 re-absorb overlapping
content.
