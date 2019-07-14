# instructions for the register machine are of the form
#
# increment register:
#   <label><register>++[next]

# decrement register:
#   <label><register>--<jump>[:next]

# next defaults to label+1
# if register is empty, it does not decrement and pc=jump

# label is an integer
# register starts with a letter

import fileinput
import re
from dataclasses import dataclass
from collections import defaultdict

FMT = re.compile(r"""
    (?P<label>\d+)(?P<register>\w+)(?P<op>[+-]+)(?P<label1>\d+)?(:(?P<label2>\d+))?
""", re.VERBOSE)

@dataclass
class Instr:
    label: int
    register: str
    op: str
    jump: int
    next: int

    def parse(line):
        match = FMT.match(line)
        l0 = int(match.group("label"))
        l1 = match.group("label1")
        l2 = match.group("label2")
        return Instr(
            l0,
            match.group("register"),
            match.group("op"),
            int(l1) if l1 else l0+1,
            int(l2) if l2 else l0+1,
        )

instrs = [Instr.parse(line) for line in fileinput.input()]
prog = {instr.label: instr  for instr in instrs}

pc = 1
regs = defaultdict(int)

while pc in prog:
    c = prog[pc]
    print(regs)
    if c.op == "++":
        regs[c.register] += 1
        pc = c.next
    elif c.op == "--":
        if regs[c.register] > 0:
            regs[c.register] -= 1
            pc = c.next
        else:
            pc = c.jump
    else:
        break
