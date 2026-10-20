#!/usr/bin/env python3
"""A readable version of K230, the 230-state Turing machine that halts iff ZFC is inconsistent.

Source: https://github.com/elliotglazer/k230-rocq

The Turing machine runs a register machine program (machine/sites230.json in that repo).
That program is a proof search, and the Rocq development proves that one pass of its main
loop computes exactly `enum_step` below (coq/logic/Enum230.v, coq/prog/L2Root230.v).
This file transcribes that spec. It halts iff some natural number decodes to a derivation
of falsity in a compact set theory K (plus irreflexivity) that is equiconsistent with ZFC.

Run `python3 k230.py` to search, printing each command. To compare this spec against the
real compiled register-machine program, step by step, run
`python3 k230.py --check path/to/sites230.json`.

Do not expect it to get far. Formula codes are nested Cantor pairs, and each nesting
level roughly doubles their bit length. The first K axiom the search builds, at command 10
(bundle(3, 0, 1)), is a number of about 4e8 bits. Each later push doubles the stack's size
again. The Turing machine, which does this arithmetic in unary, is far slower still. A
faithful transcription inherits the same blowup. The register-machine check is
practical only for the first 4 commands, before the stack becomes huge.
"""

import argparse
from math import isqrt


# ---------------------------------------------------------------------------
# Numbers as pairs: the Cantor pairing function and its inverse
# ---------------------------------------------------------------------------

def pair(a, b):
    """P(a, b) = tri(a + b) + b, where tri(n) = n(n+1)/2."""
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(z):
    """The inverse of pair. unpair(0) = (0, 0), so a stack of 0 behaves like endless zeros."""
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
# The proof checker
#
# Every number is a candidate proof: a list of commands encoded with `pair`. The checker
# keeps a stack of proven formulas (top `tw`, the rest `ws` encoded as nested pairs) and
# one more proven formula, the cache `h`. Everything it holds is a theorem, so it
# halts only if it holds FALSE.
#
#   0  MP    x       d += x. If h == (tw -> d), then tw := d and push TRUE, else tw := TRUE.
#                    h := TRUE.
#   1  DROP  x       d += x. Push tw. tw := h.
#   2  NIP   x       d += x. If h == FALSE, halt: a contradiction has been derived.
#                    Otherwise h := pop.
#   3+c  AX  x y u   d += x. With a = d and b = h + y, push tw, (forall a. h), rho8..rho1.
#                    tw := gate(a, b, c). d := 0, h := TRUE.
#
# d is the parameter counter. It is used both as a variable and as a formula code.
# ---------------------------------------------------------------------------

class State:
    __slots__ = ("pl", "np", "tw", "ws", "d", "h")

    def __init__(self, pl, np, tw, ws, d, h):
        self.pl = pl    # prooflist: the commands left in the current candidate, minus 1
        self.np = np    # nextproof: the next candidate number to try
        self.tw = tw    # topwff: the top of the stack
        self.ws = ws    # wffstack: the rest of the stack, as nested pairs
        self.d = d      # param1: the parameter counter
        self.h = h      # param2: the cached formula

    def registers(self):
        """The register file of the compiled program at a main-loop boundary (L2Root230.enc)."""
        return [self.np, self.tw, self.ws, 0, self.d, self.h, 0, 0, self.pl]


def push(x, stack): return pair(x, stack)
def pop(stack): return unpair(stack)


def step(s):
    """Run one command. Return False if it halts, i.e. if it found a proof of FALSE."""
    if s.pl == 0:
        # Start the next candidate. Its first command is read from the candidate number
        # itself. Later commands are read from pl - 1. The stack and cache carry over.
        commands, s.np = s.np, s.np + 1
    else:
        commands = s.pl - 1
    op, commands = unpair(commands)
    x, commands = unpair(commands)
    s.d += x

    if op == 0:                                     # MP
        if wim(s.tw, s.d) == s.h:
            s.tw, s.ws = s.d, push(TRUE, s.ws)
        else:
            s.tw = TRUE
        s.h = TRUE
    elif op == 1:                                   # DROP
        s.tw, s.ws = s.h, push(s.tw, s.ws)
    elif op == 2:                                   # NIP
        if s.h == FALSE:
            return False
        s.h, s.ws = pop(s.ws)
    else:                                           # AX
        c = op - 3
        y, commands = unpair(commands)
        u, commands = unpair(commands)
        a, b = s.d, s.h + y
        for f in (s.tw, wal(a, s.h), rho8(a, b, c, u), rho7(a, b, c), rho6(a, c),
                  rho5(a, b, c), rho4(a, b, c), rho3(a, b, c), rho2(a, b, c), rho1(a, b)):
            s.ws = push(f, s.ws)
        s.tw = gate(a, b, c)
        s.d, s.h = 0, TRUE
    s.pl = commands
    return True


def seed():
    """The state left by the Turing machine's 408419-step bootstrap from the blank tape:
    candidate 3, parameter counter 3. Seed230.v proves the search is still complete."""
    return State(pl=0, np=3, tw=0, ws=0, d=3, h=0)


# ---------------------------------------------------------------------------
# Optional: run the real compiled register-machine program in lockstep (RM.v, rm_step)
# ---------------------------------------------------------------------------

def load_rm(path):
    """sites230.json lists every leaf of the program tree as [bit path, operation]."""
    import json
    leaves = {}
    for bits, op in json.load(open(path)):
        name, *arg = op.split()
        leaves[bits] = (name, int(arg[0]) if arg else None)
    return leaves


def rm_run_main(leaves, regs):
    """Run main() once from an all-zero instruction pointer, the start of main.
    Return False if the program reaches the halt leaf."""
    ip = ""
    while True:
        path = ""
        while path not in leaves:                   # bits past the end of ip read as 0
            path += ip[len(path)] if len(path) < len(ip) else "0"
        op, r = leaves[path]
        if op == "EHalt":
            return False
        if op == "EInc":
            regs[r] += 1
            ip = increment(path)
        elif op == "EDecnz" and regs[r] > 0:
            regs[r] -= 1
            ip = increment(path)
        elif op in ("EDecnz", "EBreak"):            # decrement of 0 = break 1
            ip = increment(strip(path, "0", 1 if op == "EDecnz" else r))
        elif op == "EContinue":
            ip = strip(path, "1", r)
        if "1" not in ip:                           # ran off the end of main
            return True


def increment(ip):
    """Add 1 at the right end. Overflow wraps to all zeros, the start of main."""
    i = ip.rfind("0")
    return "0" * len(ip) if i < 0 else ip[:i] + "1" + "0" * (len(ip) - i - 1)


def strip(ip, bit, k):
    """Remove bits from the right until k copies of `bit` have been removed."""
    while k and ip:
        k -= ip[-1] == bit
        ip = ip[:-1]
    return ip


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


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--steps", type=int, default=None, help="stop after this many commands")
    ap.add_argument("--report", type=int, default=1, help="print progress every N commands")
    ap.add_argument("--check", metavar="SITES_JSON", help="cross-check against the compiled register machine")
    args = ap.parse_args()

    s = seed()
    leaves = regs = None
    if args.check:
        leaves = load_rm(args.check)
        regs = s.registers()

    n = 0
    while args.steps is None or n < args.steps:
        running = step(s)
        if leaves:
            if rm_run_main(leaves, regs) != running or (running and regs != s.registers()):
                raise SystemExit(f"mismatch after {n} commands: spec {s.registers()} vs rm {regs}")
        if not running:
            print(f"HALT after {n + 1} commands: derived ⊥ in candidate {s.np - 1}. ZFC is inconsistent!")
            return
        n += 1
        if n % args.report == 0:
            print(f"{n} commands, candidate {s.np}, top of stack {show(s.tw, 3)}, "
                  f"stack size {s.ws.bit_length()} bits", flush=True)
    print(f"stopped after {n} commands without finding a contradiction"
          + (" (register machine agreed at every step)" if leaves else ""))


if __name__ == "__main__":
    main()
