# Bead hub-lsb1u.4.2 — Jacquet–Langlands correspondence + multiplicity one (second independent pass)

Scope: map the JL + multiplicity-one chapter of the FLT-on-Lean route, from repo main
(`e99f167`) at /Users/kas/FLT, without consulting any prior cartography.

## 1. Where the route invokes JL / multiplicity one (evidence, file:line)

**Blueprint (LaTeX):**

- `blueprint/src/chapter/chtopbestiary.tex:212-213` — "The theorems I need are:
  Jacquet-Langlands for inner forms of $\GL_2$ over totally real fields, and multiplicity 1
  for these inner forms. We also need cyclic base change plus classification of image, all
  for totally definite quaternion algebras, and we need automorphic induction from
  $\GL_1(K)$ to $\GL_2(F)$ …"
- `blueprint/src/chapter/ch04overview.tex:30` — JL listed among the machinery for potential
  modularity.
- `blueprint/src/chapter/ch04overview.tex:86-88` — proof sketch of the modularity lifting
  theorem: "the Skinner–Wiles trick … needs cyclic base change for $\GL(2)$ and also a
  characterisation of the image of the base change construction; this seems to need a
  multiplicity one result, which (because of our definition of 'modular') will need
  Jacquet–Langlands as well."
- `blueprint/src/chapter/ch04overview.tex:94-97` — potential-modularity endpoint: the
  auxiliary mod-$p$ rep induced from a character "is associated to an automorphic
  representation of $\GL_2/F$ and hence by Jacquet–Langlands it is modular."
- `blueprint/src/chapter/QuaternionAlgebraProject.tex:155-156` — remark that
  finite-dimensionality of $S^D(U;k)$ plus JL recovers classical finite-dimensionality
  ("the Jacquet–Langlands theorem is much much harder to prove").

**Lean sources:**

- `grep -rn "Jacquet" FLT/**/*.lean` → **zero hits**. JL currently has no Lean statement.
  The only automorphy-related `multiplicity` hits are unrelated (ideal multiplicity, Sylow).
- `FLT/Assumptions/README.md` ("Forthcoming assumptions"): lists as future axioms
  "The Jacquet-Langlands correspondence between GL_2 and automorphic forms on totally
  definite quaternion algebras", "Cyclic base change for GL_2 and classification of image",
  "Automorphic induction from GL_1 to GL_2", and the note "to do the classification of image
  for cyclic base change we might well also need multiplicity 1 for GL_2, which could be a
  separate project." Crucially it also says: **"I will probably rephrase all of these goals
  in terms of Galois representations which will avoid us having to define automorphic forms
  for GL_2 directly."**
- `FLT/GaloisRepresentation/Automorphic.lean:67-94` — `GaloisRep.IsAutomorphicOfLevel`:
  "modular" is *defined* on the quaternionic side (totally definite $D/F$, discriminant 1,
  weight 2, level $U_1(S)$, an algebra hom $\pi$ from the $\mathbb{Z}_p$-Hecke algebra, with
  compatibility $\det\rho(\mathrm{Frob}_v)=N(v)$ and
  $\mathrm{tr}\,\rho(\mathrm{Frob}_v)=\pi(T_v)$ for $v\notin S\cup\{p\}$).
- `FLT/GaloisRepresentation/Automorphic.lean:127-184` — `theorem cyclic_base_change … := sorry`,
  stated purely quaternionically (the Galois-rep rephrasing in action). Its paper proof is
  where JL (both directions) + multiplicity one + classification of image live.
- `FLT/Assumptions/KnownIn1980s.lean` — the `knownin1980s` axiom/tactic; the file's own
  docstring names "Langlands on cyclic base change" as intended usage. Plan: sorry-free FLT
  using `knownin1980s` liberally, later compressed to ~10 terminal assumptions.

## 2. Architectural finding that shapes this whole bead

Because `IsAutomorphicOfLevel` is quaternionic from the start, **JL never needs to appear as
a standalone Lean theorem on this route**. It is consumed only inside the paper-level
justifications of two Galois-rep-phrased axioms:

1. **Cyclic base change** (`cyclic_base_change`, already stated, sorry'd) — paper proof:
   quaternionic eigenform → (JL, $D\to\GL_2$) Hilbert cusp form → Langlands solvable base
   change → descent/classification of image (needs mult one + strong mult one) →
   (JL, $\GL_2\to D$) back to $D_E$. This is bead **hub-lsb1u.5**'s axiom; JL is hidden in it.
2. **Automorphic induction endpoint** (not yet stated in Lean) — "irreducible mod-$p$ rep
   induced from a character of a totally imaginary quadratic $K/F$ is automorphic": theta
   series/converse theorem gives a $\GL_2/F$ form; JL ($\GL_2\to D$) lands it in $S^D$.
   Feeds off bead **hub-lsb1u.9** (CFT: characters, Hecke L-functions).

Also relevant: attaching Galois reps to quaternionic eigenforms (Taylor 1989 / Carayol 1986,
bead **hub-lsb1u.10**) historically goes *through* JL to Hilbert modular forms and Shimura
curves; the route's Hecke-compatibility-only definition means .10's axiom will also absorb a
JL use.

So there are two viable shapes:

- **Route A (matches the maintainer's stated plan, recommended):** no standalone JL/mult-one
  Lean statement. This bead's deliverable degenerates to (i) the quaternionic eigenform
  infrastructure that the axioms of beads .5/.9/.10 need to even be *stated* (largely done,
  see seeds), and (ii) `knownin1980s`-style citation notes. Bead cost: **S–M**.
- **Route B (JL as an explicit terminal assumption, needed for the "~10 assumptions" phase
  if KMB wants JL to be one of them):** requires formalizing the $\GL_2$ adelic side to
  state it. Bead cost: **L** for statements, **XL** for proofs.

## 3. Weakest sufficient JL statement for THIS route

Fix: $F$ totally real, $[F:\mathbb{Q}]$ even; $D/F$ the totally definite quaternion algebra
of **discriminant 1** (ramified at exactly the infinite places — exists iff degree even,
which is why the route restricts to even degree; see `ch04overview.tex:14-19`); weight 2
(trivial at infinity); level $U_1(S)$ (and its Taylor–Wiles variants $U_1(S,Q)$, see
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:28-33`); trivial
character; coefficients a $\overline{\mathbb{Q}}_p$-algebra via the $\mathbb{Z}_p$-Hecke
algebra.

**JL (route-minimal, eigensystem-level).** There is a bijection between
(a) Hecke eigensystems occurring in $S^D(U_1(S);\overline{\mathbb{Q}}_p)$ **excluding the
norm-factoring (one-dimensional) forms**, and
(b) cuspidal automorphic representations $\pi$ of $\GL_2(\mathbb{A}_F)$ that are discrete
series of lowest weight (= parallel weight 2, i.e. classical Hilbert cusp forms of parallel
weight 2) at every infinite place, with a $U_1(S)$-fixed vector,
matching $T_v$ (and $S_v$/central character) eigenvalues at **every** finite place — in
particular at all $v \notin S \cup \{p\}$, which is all the route's Hecke compatibility
(`Automorphic.lean:87-94`) ever inspects.

Not needed: general weights or characters, ramified $D$ (discriminant $\ne 1$), local
character identities, archimedean JL beyond weight-2 discrete series, newform/conductor
theory beyond $U_1(S)$-fixed vectors, the $\GL_n(D)$ generalizations.

Since $D$ is unramified at all finite places, the local transfer is the identity at every
finite place: JL here is exactly Eichler/Shimizu's "basis problem" setting, the historically
first and easiest case.

**Multiplicity one (route-minimal).** Two consumable forms, both used only inside bead .5's
paper proof (classification of the image of base change):
- (M1) Multiplicity one for $\GL_2/F$ cuspidal representations (JL 1970 §11, via uniqueness
  of Whittaker models).
- (M1′) Strong multiplicity one: agreement of local components at almost all $v$ forces
  $\pi_1 \cong \pi_2$ (Miyake 1971; Casselman; for the route: eigensystems at $v \notin
  S\cup\{p\}$ determine the form up to scalar in fixed level/weight).
Quaternionic corollary via JL: each non-norm-factoring eigensystem in
$S^D(U_1(S);\overline{\mathbb{Q}}_p)$ has a 1-dimensional eigenspace after newform
normalization. Needed by .5 for: $\pi$ on $\GL_2/E$ with $\pi^\sigma \cong \pi$ descends
(Langlands' characterization of the image of base change).

## 4. Node inventory (numbered; sizes S/M/L/XL)

Assumption-phase nodes (state + axiomatize):

- **N1 [L; XL if done via general $(\mathfrak{g},K)$-modules]** Adelic $\GL_2/F$ weight-2
  cusp forms / Hilbert modular forms, enough to *state* JL side (b). Blueprint bestiary
  (`chtopbestiary.tex:216`) concedes this is far off ("little point formalising the
  statements if we cannot yet even formalise the definition"). Concrete function-space
  shortcut (mirror the quaternionic `WeightTwoAutomorphicForm` design; seed
  `FLT/GlobalLanglandsConjectures/GLnDefs.lean`) keeps this L. **Route A skips N1 entirely.**
- **N2 [done/S]** Quaternionic side. Already in repo, essentially sorry-free:
  `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean` (1238 lines; forms $S^D(R)$, levels,
  characters; single `knownin1980s` at `Basic.lean:499`, a Voight 17.7.13 finiteness),
  `FiniteDimensional.lean` (finite-dimensionality, QuaternionAlgebraProject miniproject),
  `HeckeOperators/{Abstract,Local,Concrete}.lean` ($T_v$, $U_{v,a}$, `HeckeAlgebra D 𝒮` for
  levels $U_1(S,Q)$), `InnerProduct.lean` (920 lines, Petersson product, Andrew Yang 2026).
  Underpinned by `FLT/DivisionAlgebra/Finiteness.lean` (Fujisaki: finiteness of class sets).
- **N3 [M]** Semisimplicity/diagonalizability of the Hecke action on
  $S^D(U;\mathbb{C})$ (or char-0 fields) via the Petersson product (self-adjointness of
  $T_v$ up to $S_v$); eigenform decomposition. `InnerProduct.lean` is visibly built for this.
- **N4 [M]** $\mathbb{C} \leftrightarrow \overline{\mathbb{Q}}_p$ eigensystem transfer:
  Hecke eigenvalues are algebraic (finite-dimensionality + stability of an
  $\mathcal{O}_F$-lattice / Galois-descent of eigensystems), so the literature's complex JL
  statement feeds the route's $p$-adic Hecke-algebra homs. Standard but fiddly.
- **N5 [M, needs N1+N2]** Lean statement of route-minimal JL (§3), including the exclusion
  of norm-factoring forms.
- **N6 [S, needs N5]** JL as `knownin1980s`/axiom with citation (JL 1970 §16; Shimizu 1972).
- **N7 [M, needs N1 (or eigensystem phrasing via N2 only)]** Lean statement of mult one +
  strong mult one (route-minimal forms M1/M1′).
- **N8 [S, needs N7]** Mult one as axiom with citation (JL 1970 §11; Miyake 1971).

Deprecation-phase nodes (actually proving the axioms; realistically post-2029):

- **N9 [XL]** Local representation theory of $\GL_2(F_v)$: principal series, Steinberg,
  discrete series, Whittaker/Kirillov models, spherical Hecke ↔ Satake. Nothing in Mathlib.
- **N10 [XL]** Global Whittaker expansion + uniqueness ⇒ multiplicity one (JL §11); strong
  mult one on top (L given N9–N10 core).
- **N11 [XL]** JL proof proper. Two routes: trace formula (JL §16 — "only sketched" even in
  the original per the authors' preface) or **Shimizu's theta-series construction (1972)** —
  explicit, avoids the full trace formula, and in the discriminant-1 totally definite case is
  close to Eichler's basis-problem computations; the more formalizable route, but still XL
  (Weil representations, theta lifts, Siegel–Weil ingredients).

Node count: **11** (8 assumption-phase, 3 deprecation-phase). Route A collapses the
assumption phase to N2+N3+N4 plus citation comments inside beads .5/.9/.10's axioms.

## 5. Dependency edges

Internal: N5 ← N1,N2; N6 ← N5; N7 ← N1 (or N2-only phrasing); N8 ← N7; N3 ← N2;
N4 ← N2,N3; N10 ← N9; N11 ← N9 (+N3 for the comparison of inner products / Petersson).

External beads:
- **hub-lsb1u.5 (cyclic base change):** primary consumer. Its axiom
  (`Automorphic.lean:127`, sorry) hides JL(both directions) + M1 + M1′ + Langlands'
  image classification. Any change to the JL statement shape must be negotiated with .5.
- **hub-lsb1u.9 (CFT):** supplies Hecke characters/L-functions for the automorphic-induction
  endpoint whose final step is JL ($\GL_2\to D$); also solvable-extension existence.
- **hub-lsb1u.10 (Galois reps):** Taylor 1989/Carayol 1986 attachment of $\rho_\pi$ to
  quaternionic eigenforms — Taylor's method is itself quaternionic-congruence based (good fit
  for this route's definition), but its published proof routes through JL to Hilbert modular
  forms; .10's axiom will absorb that use.
- Mathlib seeds (inspected `.lake/packages/mathlib`): `Mathlib.NumberTheory.ModularForms.*`
  (classical level-1/congruence modular forms, Petersson.lean — **not** adelic, not Hilbert),
  `Mathlib.Algebra.Quaternion` (concrete Hamilton quaternions; FLT instead uses its own
  `FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean`), `Mathlib.NumberTheory.HeckeRing` (abstract).
  No adelic automorphic forms, no smooth representation theory of $p$-adic groups, no
  Whittaker models in Mathlib. Repo seeds: the 3801-line
  `FLT/AutomorphicForm/QuaternionAlgebra/` stack, `FLT/GlobalLanglandsConjectures/GLnDefs.lean`,
  `FLT/DivisionAlgebra/Finiteness.lean`.

## 6. Risks

- **R1 (highest):** Route B is blocked on defining $\GL_2$ adelic automorphic forms (N1),
  which the blueprint itself flags as not yet feasible. Mitigation: Route A, per the
  Assumptions README's explicit rephrasing plan — but then this bead must coordinate with .5
  and .10 so the JL content is correctly attributed inside *their* axioms, not dropped.
- **R2 (statement drift):** the route hardwires discriminant 1, weight 2, $U_1(S,Q)$ levels
  (including Taylor–Wiles $Q$-levels with $U_{v,a}$ operators). A JL/mult-one statement
  matching only $U_1(S)$ would silently under-serve the patching argument.
- **R3 (norm-factoring forms):** $S^D$ for totally definite $D$ contains 1-dimensional
  forms factoring through the reduced norm; JL matches only their complement. A naive
  "bijection of all eigensystems" statement is **false**. Mult one similarly needs the
  exclusion.
- **R4 (coefficient mismatch):** literature is over $\mathbb{C}$; route is
  $\mathbb{Z}_p/\overline{\mathbb{Q}}_p$ Hecke-algebra homs. N4 is unavoidable and easy to
  underestimate (choice of $\mathbb{C}\cong\overline{\mathbb{Q}}_p$ vs. algebraicity route).
- **R5:** JL §16's original proof is sketched even per its authors; for eventual
  deprecation, Shimizu's theta construction is the safer formalization target, but no one
  has formalized any theta correspondence anywhere.

## 7. Size verdict

- **Route A (recommended, matches repo trajectory): S–M** for this bead — the quaternionic
  infrastructure is already built; remaining work is N3+N4 plus precise
  `knownin1980s` citation scaffolding, with JL/mult-one absorbed into beads .5/.9/.10's axioms.
- **Route B (explicit JL + mult-one terminal assumptions): L** (dominated by N1).
- **Full deprecation (proving JL + mult one in Lean): XL**, multi-year; not on the critical
  path before the 2029 assumption-phase target.

## 8. Verified citations

- Jacquet–Langlands, *Automorphic Forms on GL(2)*, Springer LNM 114, 1970 — correspondence
  in §16 (trace formula, sketched per authors' preface), multiplicity one in §11. Full text:
  https://publications.ias.edu/sites/default/files/automorphic-forms-on-gl2_rpl_8.pdf ;
  context: https://en.wikipedia.org/wiki/Jacquet%E2%80%93Langlands_correspondence ,
  https://en.wikipedia.org/wiki/Automorphic_Forms_on_GL(2)
- Shimizu, "Theta series and automorphic forms on GL₂", J. Math. Soc. Japan 24 (1972),
  638–683 (+ correction, JMSJ 26 (1974), 374–376) — explicit theta-lift construction of JL;
  solves the basis problem in the totally definite setting.
  https://www.jstage.jst.go.jp/article/jmath1948/24/4/24_4_638/_article ;
  https://projecteuclid.org/journals/journal-of-the-mathematical-society-of-japan/volume-26/issue-2/A-correction-to--Theta-series-and-automorphic-forms-on/10.2969/jmsj/02620374.full
- Taylor, "On Galois representations associated to Hilbert modular forms", Invent. Math. 98
  (1989), 265–280, DOI 10.1007/BF01388853 — Galois reps via totally definite quaternion
  algebras over even-degree $F$; the template for this route's definitions.
  https://link.springer.com/article/10.1007/BF01388853
- Cited but not independently re-verified this pass (standard): Langlands, *Base Change for
  GL(2)*, Ann. of Math. Studies 96, 1980 (bead .5's core reference; image classification);
  Miyake, "On automorphic forms on GL₂ and Hecke operators", Ann. of Math. 94 (1971) (strong
  mult one); Carayol, Ann. Sci. ÉNS 19 (1986); Voight, *Quaternion Algebras*, GTM 288
  (cited in-repo at `Basic.lean:492`, "Lemma 17.7.13 in Voight").
