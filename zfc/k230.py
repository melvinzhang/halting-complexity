#!/usr/bin/env python3
"""A readable version of K230, the 230-state Turing machine that halts iff ZFC is inconsistent.

Source: https://github.com/elliotglazer/k230-rocq

The machine is a proof search. It tries every natural number as a proof and halts iff
one of them derives falsity in a compact set theory K (plus irreflexivity), which the
Rocq development proves equiconsistent with ZFC. This file follows the spec of that
search in coq/logic/Enum230.v, which the Rocq proof shows the machine computes exactly.

Run `python3 k230.py` to search, printing each command.

Do not expect it to get far. Formula codes are nested Cantor pairs, and each nesting
level roughly doubles their bit length. The first K axiom the search builds, at command 10
(bundle(3, 0, 1)), is a number of about 4e8 bits. The Turing machine, which does this
arithmetic in unary, is far slower still.
"""

from itertools import count
from math import isqrt


# ---------------------------------------------------------------------------
# Numbers as pairs: the Cantor pairing function and its inverse
# ---------------------------------------------------------------------------

def pair(a, b):
    """P(a, b) = tri(a + b) + b, where tri(n) = n(n+1)/2."""
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(z):
    """The inverse of pair. unpair(0) = (0, 0)."""
    s = (isqrt(8 * z + 1) - 1) // 2
    b = z - s * (s + 1) // 2
    return s - b, b


# ---------------------------------------------------------------------------
# Formulas as numbers. Variables are natural numbers. Code 0 is "true" (0 = wim(0, 0)).
# ---------------------------------------------------------------------------

def wim(a, b): return 4 * pair(a, b)          # a -> b
def wel(i, j): return 4 * pair(i, j) + 1      # x_i in x_j
def wal(i, a): return 4 * pair(i, a) + 2      # forall x_i. a
def weq(i, j): return 4 * pair(i, j) + 3      # x_i = x_j


FALSE = 1                                     # wel(0, 0): "x0 in x0", false by irreflexivity
TRUE = 0


def wn(a): return wim(a, FALSE)               # not a
def wa(a, b): return wn(wim(a, wn(b)))        # a and b
def wex(x, a): return wn(wal(x, wn(a)))       # exists x. a


# ---------------------------------------------------------------------------
# Axioms of first-order logic with equality (one row per axiom scheme)
# ---------------------------------------------------------------------------

def rho1(a, b):       return wex(a, weq(a, b))                                     # exists a. a = b
def rho2(a, b, c):    return wim(wal(a, wim(b, c)), wim(wal(a, b), wal(a, c)))     # quantified modus ponens
def rho3(a, b, c):    return wim(weq(a, b), wim(wel(c, a), wel(c, b)))             # a = b -> (c in a -> c in b)
def rho4(a, b, c):    return wim(wal(a, wal(b, c)), wal(b, wal(a, c)))             # swap quantifiers
def rho5(a, b, c):    return wim(weq(c, a), wim(wel(c, b), wel(a, b)))             # c = a -> (c in b -> a in b)
def rho6(a, b):       return wim(wex(a, wal(a, b)), b)                             # (exists a. forall a. b) -> b
def rho7(a, b, c):    return wim(weq(c, a), wim(weq(c, b), weq(a, b)))             # Euclid for equality
def rho8(a, b, c, u): return wim(wim(wim(c, u), a), wim(wim(a, c), wim(b, c)))     # Lukasiewicz's single axiom


# ---------------------------------------------------------------------------
# The theory K: a single axiom scheme replacing all of ZFC's set-existence axioms
#
#   For any formula phi(y, p, q):
#     p ⊆ u    := forall z (z in p -> z in u)
#     W(p, C)  := (exists y phi(y,p,q)) -> exists y (y in C and phi(y,p,q))
#     H(C)     := forall u (u in C -> ((exists p phi(u,p,q)) and forall p (p ⊆ u -> W(p, C))))
#   Axiom:  forall a forall x exists C ((phi(x,a,q) -> x in C) and H(C))
#
# Here a is the input variable, b is the output variable, and c is both the variable
# for C and (since formulas are numbers) the code of the formula phi. The scheme is
# emitted with its conjunctions reversed. The proof shows this is the same theory.
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
    return wa(kcore(a, b, c, c), vacuity(a, b, c))


def gate(a, b, c):
    """A K axiom, only when variable c is distinct from a and b; otherwise just TRUE."""
    return TRUE if c in (a, b) else bundle(a, b, c)


# ---------------------------------------------------------------------------
# Proofs as numbers
#
# A proof is a list of commands. Each command is an opcode and some numeric fields:
#
#   op 0      MP    x
#   op 1      DROP  x
#   op 2      NIP   x
#   op 3 + c  AX    x y u
#
# The number n decodes as op, x (and y, u for AX), then the rest r. If r is 0 the proof
# ends. Otherwise the next command is decoded from r - 1.
# ---------------------------------------------------------------------------

def commands(n):
    while True:
        op, n = unpair(n)
        x, n = unpair(n)
        if op >= 3:
            y, n = unpair(n)
            u, n = unpair(n)
            yield op, x, y, u
        else:
            yield op, x, None, None
        if n == 0:
            return
        n -= 1


# ---------------------------------------------------------------------------
# The proof checker
#
# It keeps a stack of proven formulas and one more proven formula, the cache. It halts
# only if the cache is FALSE. The stack, the cache and the parameter counter d carry
# over from one proof to the next. Popping an empty stack gives TRUE.
#
#   MP    x       d += x. If cache == (top -> d), replace top by d and push TRUE under it.
#                 Otherwise replace top by TRUE. Then cache := TRUE.
#   DROP  x       d += x. Push cache.
#   NIP   x       d += x. If cache == FALSE, halt: a contradiction has been derived.
#                 Otherwise pop the formula under top into cache.
#   AX c  x y u   d += x. With a = d and b = cache + y, push (forall a. cache), rho8..rho1,
#                 and K axiom gate(a, b, c). Then d := 0, cache := TRUE.
#
# d is used both as a variable and as a formula code.
# ---------------------------------------------------------------------------

class Contradiction(Exception):
    pass


class Checker:
    def __init__(self):
        # The Turing machine's 408419-step bootstrap from the blank tape leaves the search
        # at proof 3 with d = 3. Seed230.v proves the search is still complete from there.
        self.top = TRUE
        self.rest = []
        self.cache = TRUE
        self.d = 3

    def pop(self):
        return self.rest.pop() if self.rest else TRUE

    def run(self, op, x, y, u):
        self.d += x
        if op == 0:                                     # MP
            if wim(self.top, self.d) == self.cache:
                self.rest.append(TRUE)
                self.top = self.d
            else:
                self.top = TRUE
            self.cache = TRUE
        elif op == 1:                                   # DROP
            self.rest.append(self.top)
            self.top = self.cache
        elif op == 2:                                   # NIP
            if self.cache == FALSE:
                raise Contradiction
            self.cache = self.pop()
        else:                                           # AX
            c, a, b = op - 3, self.d, self.cache + y
            self.rest += [self.top, wal(a, self.cache), rho8(a, b, c, u), rho7(a, b, c),
                          rho6(a, c), rho5(a, b, c), rho4(a, b, c), rho3(a, b, c),
                          rho2(a, b, c), rho1(a, b)]
            self.top = gate(a, b, c)
            self.d, self.cache = 0, TRUE


# ---------------------------------------------------------------------------

def show(f, depth=6):
    """Pretty-print a formula code."""
    if f == TRUE: return "⊤"
    if f == FALSE: return "⊥"
    if depth == 0: return "…"
    tag, (i, j) = f % 4, unpair(f // 4)
    if tag == 0:
        return "¬" + show(i, depth - 1) if j == FALSE else f"({show(i, depth - 1)} → {show(j, depth - 1)})"
    if tag == 1: return f"x{i} ∈ x{j}"
    if tag == 2: return f"∀x{i} {show(j, depth - 1)}"
    return f"x{i} = x{j}"


NAMES = {0: "MP", 1: "DROP", 2: "NIP"}


def main():
    checker = Checker()
    for proof in count(3):
        for op, x, y, u in commands(proof):
            name = NAMES.get(op, f"AX {op - 3}")
            print(f"proof {proof}: {name} {x}" + (f" {y} {u}" if op >= 3 else ""), end="", flush=True)
            try:
                checker.run(op, x, y, u)
            except Contradiction:
                print(f"\nproof {proof} derives ⊥. ZFC is inconsistent!")
                return
            print(f"  ->  top {show(checker.top, 3)}, stack depth {len(checker.rest)}")


if __name__ == "__main__":
    main()
