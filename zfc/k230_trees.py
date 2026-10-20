#!/usr/bin/env python3
"""A fast search that halts iff ZFC is inconsistent, using the proof system of K230.

Source: https://github.com/elliotglazer/k230-rocq

k230.py follows the 230-state Turing machine step by step. That machine stores formulas
as numbers, and those numbers reach billions of bits within a few hundred commands.
This program searches the same proof system (coq/logic/Thm230.v) but stores formulas as
trees. It is not the machine, but it halts under the same condition: the Rocq development
proves that this proof system derives FALSE iff ZFC is inconsistent
(Bridge230.thm230_iff_KPrimeOrdIR and KUpperConsistency.v).

Usage: python3 k230_trees.py [number of derivations to check]
"""

import sys
from itertools import count
from math import isqrt


def pair(a, b):
    """The Cantor pairing function P(a, b) = tri(a + b) + b."""
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(z):
    s = (isqrt(8 * z + 1) - 1) // 2
    b = z - s * (s + 1) // 2
    return s - b, b


def split(n, k):
    """Split n into k numbers. Every k-tuple comes from exactly one n."""
    parts = []
    for _ in range(k - 1):
        first, n = unpair(n)
        parts.append(first)
    return parts + [n]


# ---------------------------------------------------------------------------
# Formulas as trees. Variables are natural numbers.
# ---------------------------------------------------------------------------

TRUE = ("true",)


def wim(a, b):                                  # a -> b
    # The machine codes TRUE as 0 = code(TRUE -> TRUE), so these are the same formula.
    return TRUE if a == TRUE and b == TRUE else ("imp", a, b)


def wel(i, j): return ("in", i, j)              # x_i in x_j
def wal(i, a): return ("all", i, a)             # forall x_i. a
def weq(i, j): return ("eq", i, j)              # x_i = x_j


FALSE = wel(0, 0)                               # "x0 in x0", false by irreflexivity


def wn(a): return wim(a, FALSE)                 # not a
def wa(a, b): return wn(wim(a, wn(b)))          # a and b
def wex(x, a): return wn(wal(x, wn(a)))         # exists x. a


def decode(n):
    """The formula that the machine codes as n. Every number is some formula."""
    if n == 0:
        return TRUE
    i, j = unpair(n // 4)
    return (lambda: wim(decode(i), decode(j)), lambda: wel(i, j),
            lambda: wal(i, decode(j)), lambda: weq(i, j))[n % 4]()


# ---------------------------------------------------------------------------
# Axioms of first-order logic with equality. a, b, c are variables, p, q, r, s formulas.
# ---------------------------------------------------------------------------

def rho1(a, b):       return wex(a, weq(a, b))                                     # exists a. a = b
def rho2(a, p, q):    return wim(wal(a, wim(p, q)), wim(wal(a, p), wal(a, q)))     # quantified modus ponens
def rho3(a, b, c):    return wim(weq(a, b), wim(wel(c, a), wel(c, b)))             # a = b -> (c in a -> c in b)
def rho4(a, b, p):    return wim(wal(a, wal(b, p)), wal(b, wal(a, p)))             # swap quantifiers
def rho5(a, b, c):    return wim(weq(c, a), wim(wel(c, b), wel(a, b)))             # c = a -> (c in b -> a in b)
def rho6(a, p):       return wim(wex(a, wal(a, p)), p)                             # (exists a. forall a. p) -> p
def rho7(a, b, c):    return wim(weq(c, a), wim(weq(c, b), weq(a, b)))             # Euclid for equality
def rho8(p, q, r, s): return wim(wim(wim(r, s), p), wim(wim(p, r), wim(q, r)))     # Lukasiewicz's single axiom


# ---------------------------------------------------------------------------
# The theory K: a single axiom scheme replacing all of ZFC's set-existence axioms
#
#   For any formula phi(y, p, q):
#     p ⊆ u    := forall z (z in p -> z in u)
#     W(p, C)  := (exists y phi(y,p,q)) -> exists y (y in C and phi(y,p,q))
#     H(C)     := forall u (u in C -> ((exists p phi(u,p,q)) and forall p (p ⊆ u -> W(p, C))))
#   Axiom:  forall a forall x exists C ((phi(x,a,q) -> x in C) and H(C))
#
# Here a is the input variable and b the output variable. A single number c names both
# the variable for C and the formula phi = decode(c). The scheme is emitted with its
# conjunctions reversed. The Rocq proof shows this is the same theory.
# ---------------------------------------------------------------------------

def ksubset(a, b, k):
    return wal(k, wim(wel(k, a), wel(k, b)))                                      # a ⊆ b, via x_k


def krequest(b, k, m):
    return wal(b, wim(m, wex(b, wa(m, wel(b, k)))))                               # W(a, C)


def kcore(a, b, k, m):
    return wex(k, wa(wim(m, wel(b, k)),                                           # exists C ((phi -> b in C)
                     wal(b, wim(wel(b, k),                                        #   and forall b (b in C ->
                         wex(a, wa(m, wal(a, wim(ksubset(a, b, k),               #     exists a (phi and forall a (a ⊆ b ->
                                                 krequest(b, k, m)))))))))      #       W(a, C))))))


def vacuity(a, b, c):
    """Atomic facts do not depend on the unused variable c."""
    return wa(wim(wel(a, b), wal(c, wel(a, b))),
              wim(weq(a, b), wal(c, weq(a, b))))


def bundle(a, b, c):
    return wa(kcore(a, b, c, decode(c)), vacuity(a, b, c))


# ---------------------------------------------------------------------------
# The proof system (Thm230.v): TRUE, modus ponens, generalization, rho1..rho8, and
# bundle(a, b, c) whenever c differs from a and b.
#
# Every number n is a derivation: n % len(RULES) picks the rule, and n // len(RULES)
# holds its arguments. A premise is the number of an earlier derivation, so it is less
# than n, and the search can look up the conclusions it has already found. A step that
# does not apply concludes TRUE, as in the machine.
# ---------------------------------------------------------------------------

conclusions = []                                # conclusions[k] = what derivation k proves


def proved(k):
    while len(conclusions) <= k:
        conclusions.append(derive(len(conclusions)))
    return conclusions[k]


def mp(p, q):
    """From p and p -> b, conclude b."""
    a, b = proved(p), proved(q)
    return b[2] if b[0] == "imp" and b[1] == a else TRUE


def gen(a, p):
    """From h, conclude forall x_a. h."""
    return wal(a, proved(p))


def ax_bundle(a, b, c):
    return TRUE if c in (a, b) else bundle(a, b, c)


RULES = [
    (0, lambda: TRUE),
    (2, mp),
    (2, gen),
    (2, rho1),
    (3, lambda a, p, q: rho2(a, decode(p), decode(q))),
    (3, rho3),
    (3, lambda a, b, p: rho4(a, b, decode(p))),
    (3, rho5),
    (2, lambda a, p: rho6(a, decode(p))),
    (3, rho7),
    (4, lambda p, q, r, s: rho8(decode(p), decode(q), decode(r), decode(s))),
    (3, ax_bundle),
]


def derive(n):
    args, rule = divmod(n, len(RULES))
    arity, conclude = RULES[rule]
    return conclude(*split(args, arity)) if arity else conclude()


# ---------------------------------------------------------------------------

def show(f):
    if f == TRUE: return "⊤"
    if f == FALSE: return "⊥"
    tag, x, y = f
    if tag == "imp":
        return "¬" + show(x) if y == FALSE else f"({show(x)} → {show(y)})"
    if tag == "in": return f"x{x} ∈ x{y}"
    if tag == "all": return f"∀x{x} {show(y)}"
    return f"x{x} = x{y}"


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else None
    for n in count():
        if n == limit:
            print(f"checked {n:,} derivations without finding a contradiction")
            return
        if derive(n) == FALSE:
            print(f"derivation {n} proves ⊥. ZFC is inconsistent!")
            return
        if n and n % 1_000_000 == 0:
            print(f"{n:,} derivations checked", flush=True)


if __name__ == "__main__":
    main()
