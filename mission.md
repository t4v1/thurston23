## Motivation

In the last of the twenty-four questions that closed his 1982 survey
*Three-dimensional manifolds, Kleinian groups and hyperbolic geometry*
(Bull. Amer. Math. Soc. **6** (1982), 357–381), Thurston asked whether the
volumes of hyperbolic $3$-manifolds are rationally independent. Twenty-two of
the twenty-four have since been answered — geometrization by Perelman, tameness
by Agol and by Calegari–Gabai, the ending lamination conjecture by
Brock–Canary–Minsky, virtual fibering by Agol — and this one is among the two
that remain open.

Read literally the question has a negative answer, and for a trivial reason: a
degree $n$ cover of a hyperbolic $3$-manifold has $n$ times its volume, so any
two commensurable manifolds have rationally related volumes. The question as it
is understood, and as it is open, is whether *every* rational relation arises
that way — equivalently, whether some two hyperbolic $3$-manifolds have
irrational volume ratio. Remarkably, not a single such pair is known.

## Setting

The bundle fixes the meaning of every term. Hyperbolic $3$-space is the upper
half-space $\{(x,y,z) : z > 0\}$. Its volume is Lebesgue measure with density
$z^{-3}$ — the Riemannian volume of the metric $(dx^2+dy^2+dz^2)/z^2$ written
out, so that no Riemannian machinery is required. The hyperbolic distance is
given by its closed formula
$$\cosh d(p,q) \;=\; 1 + \frac{|p-q|^2}{2\,p_3\,q_3}.$$
A Kleinian action is a free, properly discontinuous action by hyperbolic
isometries; the quotient is a complete hyperbolic $3$-manifold, discreteness and
torsion freeness being consequences rather than hypotheses. The volume of the
quotient is the measure of a fundamental domain, in the sense of Mathlib's
`MeasureTheory.IsFundamentalDomain`, and the set of volumes collects those that
are finite and positive.

Two conventions are stated rather than derived, and are worth flagging.
Isometries are not required to preserve orientation, so the set of volumes also
contains those of non-orientable quotients; this enlarges the set but not its
$\mathbb{Q}$-span, so neither goal is affected. And preservation of the
hyperbolic volume is a field of the structure rather than a consequence of
preserving the distance: it holds for every hyperbolic isometry, but deriving it
amounts to classifying $\mathrm{Isom}(\mathbb{H}^3)$, which is not the subject
of this mission.

## Formalization targets

The goal is that the volumes are not all rationally related: there are two of
them, $v$ and $w$, with $v \neq q w$ for every rational $q$.

Two milestones support it. The first is that passing to a subgroup of index $n$
multiplies the volume by $n$, a fundamental domain for the subgroup being the
union of $n$ translates of one for the whole group; this is the source of every
known rational relation, and it is what makes the literal reading of the
question false. The second is that the set of volumes is nonempty — that some
finite-volume hyperbolic $3$-manifold exists at all — without which the goal
would be vacuously false rather than open.

A stronger form of the question, that the $\mathbb{Q}$-span of the set of
volumes is infinite dimensional, is also stated.

## Significance

The question is a geometric statement whose difficulty is arithmetic. For the
Bianchi groups of an imaginary quadratic field $F$, Humbert's formula gives the
covolume as $|\delta_F|^{3/2}\zeta_F(2)/4\pi^2$, so the ratio of two such
volumes is, up to explicit algebraic factors, a ratio of Dedekind zeta values at
$2$; and Neumann and Yang showed that the Bloch invariant of a hyperbolic
$3$-manifold lies in a subgroup of finite $\mathbb{Q}$-rank determined by its
invariant trace field, so that manifolds sharing a trace field have rationally
related volumes by construction. Producing one irrational ratio therefore means
separating two such transcendentals — a statement of the same order of
difficulty as the irrationality of $\zeta(5)$. The value of formalizing the
question is not that it will be closed, but that its statement, and the
elementary relations that make its naive form false, are pinned down exactly.
